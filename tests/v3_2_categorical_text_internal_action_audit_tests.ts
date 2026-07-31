/**
 * Focused executable SYNTAX-PARITY-1C2B internal-action audit tests.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_TEXT_REVISION,
    CORE_CATEGORICAL_TEXT_INTERNAL_ACTION_AUDIT,
    CoreCategoricalProgram,
    CoreCategoricalTextBinding,
    CoreCategoricalTextError,
    CoreCategoricalTextInternalActionAuditError,
    elaborateCoreCategoricalText,
    validateCoreCategoricalTextInternalActionAudit
} from '../src/v3_2';

const sourceFile =
    'tests/fixtures/categorical-text-internal-action-audit.emdash';

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
    CORE_CATEGORICAL_TEXT_INTERNAL_ACTION_AUDIT
));

const assertAuditError = (
    mutate: (audit: any) => void,
    code: CoreCategoricalTextInternalActionAuditError['code']
): void => {
    const audit = cloneAudit();
    mutate(audit);
    assert.throws(
        () => validateCoreCategoricalTextInternalActionAudit(audit),
        error =>
            error instanceof
                CoreCategoricalTextInternalActionAuditError &&
            error.code === code
    );
};

const fixture = () => {
    const program = new CoreCategoricalProgram({
        sourceFile,
        profile: 'fibred-displayed-nd-higher-1'
    });
    const K = program.category('internal_action_K');
    const E = program.displayedFamily('internal_action_E', K);
    const D = program.displayedFamily('internal_action_D', K);
    const FF = program.displayedFunctor(
        'internal_action_FF',
        E,
        D
    );
    const GG = program.displayedFunctor(
        'internal_action_GG',
        E,
        D
    );
    const eta = program.displayedTransfor(
        'internal_action_eta',
        FF,
        GG
    );
    const x = program.object('internal_action_x', K);
    const y = program.object('internal_action_y', K);
    const p = program.hom('internal_action_p', K, x, y);
    const u = program.object(
        'internal_action_u',
        program.fibre(E, x)
    );
    const environment: readonly CoreCategoricalTextBinding[] =
        Object.freeze([
            { name: 'FF', kind: 'term', value: FF },
            { name: 'GG', kind: 'term', value: GG },
            { name: 'eta', kind: 'term', value: eta },
            { name: 'x', kind: 'term', value: x },
            { name: 'y', kind: 'term', value: y },
            { name: 'p', kind: 'term', value: p },
            { name: 'u', kind: 'term', value: u }
        ]);
    return {
        program,
        FF,
        GG,
        eta,
        x,
        y,
        p,
        u,
        environment
    };
};

const data = fixture();

const elaborate = (source: string) =>
    elaborateCoreCategoricalText(data.program, {
        source,
        sourceFile,
        environment: data.environment,
        expected: { kind: 'term' }
    });

describe('SYNTAX-PARITY-1C2B internal-action audit', () => {
    it('executes the four existing direct targets and classifiers',
        () => {
            const terms = [
                data.program.displayedFunctorFullAction(
                    data.FF,
                    data.x,
                    data.y
                ),
                data.program.displayedFunctorInternalCell(
                    data.FF,
                    data.p,
                    data.u
                ),
                data.program.displayedTransforNaturality(
                    data.eta,
                    data.p,
                    data.u
                ),
                data.program.displayedTransforInternalHomAction(
                    data.FF,
                    data.GG
                )
            ];
            assert.deepEqual(
                terms.map(term =>
                    data.program.compile(term).surfaceType.tag
                ),
                ['functor', 'hom', 'hom', 'functor']
            );
        });

    it('distinguishes object application from internal cells',
        () => {
            const transported = data.program.apply(
                data.program.apply(data.FF, data.p, {
                    expectedShape: 'transport-functor'
                }),
                data.u
            );
            const cell = data.program.displayedFunctorInternalCell(
                data.FF,
                data.p,
                data.u
            );
            assert.equal(
                data.program.compile(transported).surfaceType.tag,
                'object'
            );
            assert.equal(
                data.program.compile(cell).surfaceType.tag,
                'hom'
            );
            assert.throws(
                () => elaborate('eta p u'),
                error =>
                    error instanceof CoreCategoricalTextError &&
                    error.code === 'CATEGORICAL_REJECTION'
            );
        });

    it('anchors the pre-implementation audit after promotion', () => {
        assert.equal(
            CORE_CATEGORICAL_TEXT_INTERNAL_ACTION_AUDIT
                .prerequisite.textRevision,
            'SYNTAX-PARITY-1C2A-CATEGORICAL-TEXT-1'
        );
        assert.equal(
            CORE_CATEGORICAL_TEXT_REVISION,
            'TEXT-PARITY-MIXED-1-CATEGORICAL-TEXT-1'
        );
        assert.deepEqual(
            CORE_CATEGORICAL_TEXT_INTERNAL_ACTION_AUDIT
                .proposal.exactPositiveSources,
            [
                'fullAction FF x y',
                'fullAction FF x y p',
                'cell FF p u',
                'naturality eta p u',
                'internalHomAction FF GG',
                'internalHomAction FF GG eta'
            ]
        );
    });

    it('is deeply frozen, validates, and fails closed on drift', () => {
        const audit = CORE_CATEGORICAL_TEXT_INTERNAL_ACTION_AUDIT;
        assertDeepFrozen(audit);
        assert.doesNotThrow(
            () => validateCoreCategoricalTextInternalActionAudit()
        );
        assert.deepEqual(
            audit.proposal.operations.map(operation =>
                operation.sourceName
            ),
            [
                'fullAction',
                'cell',
                'naturality',
                'internalHomAction'
            ]
        );
        assertAuditError(
            candidate => {
                candidate.prerequisite.textRevision = 'stale';
            },
            'TEXT_INTERNAL_ACTION_PREREQUISITE_DRIFT'
        );
        assertAuditError(
            candidate => {
                candidate.authority.activeOwners[0] = 'stale';
            },
            'TEXT_INTERNAL_ACTION_AUTHORITY_DRIFT'
        );
        assertAuditError(
            candidate => {
                candidate.proposal.operations[0].sourceName = 'stale';
            },
            'TEXT_INTERNAL_ACTION_PROPOSAL_DRIFT'
        );
        assertAuditError(
            candidate => {
                candidate.semanticDelta.programMethods = 1;
            },
            'TEXT_INTERNAL_ACTION_BOUNDARY_DRIFT'
        );
    });
});
