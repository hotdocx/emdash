/**
 * Focused executable SYNTAX-PARITY-1C2 displayed-constructor audit tests.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_TEXT_DISPLAYED_CONSTRUCTOR_AUDIT,
    CORE_CATEGORICAL_TEXT_REVISION,
    CoreCategoricalProgram,
    CoreCategoricalTextBinding,
    CoreCategoricalTextDisplayedConstructorAuditError,
    CoreCategoricalTextError,
    elaborateCoreCategoricalText,
    validateCoreCategoricalTextDisplayedConstructorAudit
} from '../src/v3_2';

const sourceFile =
    'tests/fixtures/categorical-text-displayed-constructor-audit.emdash';

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
    CORE_CATEGORICAL_TEXT_DISPLAYED_CONSTRUCTOR_AUDIT
));

const assertAuditError = (
    mutate: (audit: any) => void,
    code:
        CoreCategoricalTextDisplayedConstructorAuditError['code']
): void => {
    const audit = cloneAudit();
    mutate(audit);
    assert.throws(
        () =>
            validateCoreCategoricalTextDisplayedConstructorAudit(
                audit
            ),
        error =>
            error instanceof
                CoreCategoricalTextDisplayedConstructorAuditError &&
            error.code === code
    );
};

const fixture = () => {
    const program = new CoreCategoricalProgram({
        sourceFile,
        profile: 'fibred-displayed-chain-2a'
    });
    const K = program.category('displayed_constructor_K');
    const X = program.category('displayed_constructor_X');
    const E = program.displayedFamily(
        'displayed_constructor_E',
        K
    );
    const B = program.displayedFamily(
        'displayed_constructor_B',
        K
    );
    const C = program.displayedFamily(
        'displayed_constructor_C',
        K
    );
    const FF = program.displayedFunctor(
        'displayed_constructor_FF',
        E,
        B
    );
    const GG = program.displayedFunctor(
        'displayed_constructor_GG',
        E,
        C
    );
    const F0 = program.displayedFunctor(
        'displayed_constructor_F0',
        E,
        B
    );
    const F1 = program.displayedFunctor(
        'displayed_constructor_F1',
        E,
        B
    );
    const F2 = program.displayedFunctor(
        'displayed_constructor_F2',
        E,
        B
    );
    const eta = program.displayedTransfor(
        'displayed_constructor_eta',
        F0,
        F1
    );
    const theta = program.displayedTransfor(
        'displayed_constructor_theta',
        F1,
        F2
    );
    const x = program.object('displayed_constructor_x', K);
    const y = program.object('displayed_constructor_y', K);
    const p = program.hom(
        'displayed_constructor_p',
        K,
        x,
        y
    );
    const u = program.object(
        'displayed_constructor_u',
        program.fibre(E, x)
    );
    const v = program.object(
        'displayed_constructor_v',
        program.fibre(E, y)
    );
    const transport = program.familyTransport(E, p);
    const transportedU = program.apply(transport, u);
    const alpha = program.hom(
        'displayed_constructor_alpha',
        program.fibre(E, y),
        transportedU,
        v
    );
    const F = program.functor('displayed_constructor_F', X, K);
    const environment: readonly CoreCategoricalTextBinding[] =
        Object.freeze([
            { name: 'K', kind: 'category', value: K },
            { name: 'X', kind: 'category', value: X },
            { name: 'E', kind: 'displayed-family', value: E },
            { name: 'B', kind: 'displayed-family', value: B },
            { name: 'C', kind: 'displayed-family', value: C },
            { name: 'FF', kind: 'term', value: FF },
            { name: 'GG', kind: 'term', value: GG },
            { name: 'F0', kind: 'term', value: F0 },
            { name: 'F1', kind: 'term', value: F1 },
            { name: 'F2', kind: 'term', value: F2 },
            { name: 'eta', kind: 'term', value: eta },
            { name: 'theta', kind: 'term', value: theta },
            { name: 'x', kind: 'term', value: x },
            { name: 'y', kind: 'term', value: y },
            { name: 'p', kind: 'term', value: p },
            { name: 'u', kind: 'term', value: u },
            { name: 'v', kind: 'term', value: v },
            { name: 'alpha', kind: 'term', value: alpha },
            { name: 'F', kind: 'term', value: F }
        ]);
    return {
        program,
        E,
        B,
        C,
        FF,
        GG,
        eta,
        theta,
        x,
        y,
        p,
        u,
        v,
        alpha,
        F,
        transport,
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

describe('SYNTAX-PARITY-1C2 displayed-constructor audit', () => {
    it('executes all twelve proposed existing direct targets', () => {
        const terms = [
            data.program.displayedProductLeftProjection(
                data.B,
                data.C
            ),
            data.program.displayedProductRightProjection(
                data.B,
                data.C
            ),
            data.program.displayedProductPair(data.FF, data.GG),
            data.program.displayedProductSwap(data.B, data.C),
            data.program.displayedProductDiagonal(data.B),
            data.program.sigmaProjection(data.E),
            data.program.pullbackDisplayedFunctor(data.FF, data.F),
            data.program.dependentPair(data.E, data.x, data.u),
            data.transport,
            data.program.sigmaArrow(
                data.E,
                data.u,
                data.v,
                data.p,
                data.alpha
            ),
            data.program.pullbackTotal(data.F, data.E),
            data.program.composeDisplayedTransfor(
                data.theta,
                data.eta
            )
        ];
        assert.equal(terms.length, 12);
        for (const term of terms) {
            const compilation = data.program.compile(term);
            assert.notEqual(compilation.explicitCore.length, 0);
            assert.notEqual(compilation.explicitInferredType.length, 0);
        }
    });

    it('keeps component and point observations on generic application',
        () => {
            assert.equal(
                CORE_CATEGORICAL_TEXT_REVISION,
                'SYNTAX-PARITY-1C1-CATEGORICAL-TEXT-1'
            );
            const component = elaborate('eta x');
            const point = elaborate('eta x u');
            assert.equal(
                data.program.compare(
                    component,
                    data.program.displayedTransforComponent(
                        data.eta,
                        data.x
                    )
                ).status,
                'equal'
            );
            assert.equal(
                data.program.compare(
                    point,
                    data.program.displayedTransforPoint(
                        data.eta,
                        data.x,
                        data.u
                    )
                ).status,
                'equal'
            );
        });

    it('measures naturality and named constructors as non-generic',
        () => {
            assert.throws(
                () => elaborate('eta p u'),
                error =>
                    error instanceof CoreCategoricalTextError &&
                    error.code === 'CATEGORICAL_REJECTION'
            );
            assert.equal(
                data.program.compile(
                    data.program.displayedTransforNaturality(
                        data.eta,
                        data.p,
                        data.u
                    )
                ).surfaceType.tag,
                'hom'
            );
            assert.throws(
                () => elaborate('sigmaPair E x u'),
                error =>
                    error instanceof CoreCategoricalTextError &&
                    error.code === 'UNKNOWN_IDENTIFIER'
            );
        });

    it('freezes the corrected split and bounded proposal', () => {
        const audit =
            CORE_CATEGORICAL_TEXT_DISPLAYED_CONSTRUCTOR_AUDIT;
        assert.deepEqual(
            audit.split.map(entry => entry.row),
            [
                'SYNTAX-PARITY-1C2A',
                'SYNTAX-PARITY-1C2B',
                'SYNTAX-PARITY-1C3'
            ]
        );
        assert.equal(audit.proposal.operations.length, 12);
        assert.deepEqual(
            audit.correctedResidualInventory
                .genericApplicationAlreadyTextual
                .map(entry => entry.source),
            ['eta x', 'eta x u']
        );
        assert.equal(
            audit.correctedResidualInventory
                .explicitActionConstructorsStillRequired.length,
            4
        );
    });

    it('is deeply frozen, validates, and fails closed on drift', () => {
        assertDeepFrozen(
            CORE_CATEGORICAL_TEXT_DISPLAYED_CONSTRUCTOR_AUDIT
        );
        assert.doesNotThrow(
            () =>
                validateCoreCategoricalTextDisplayedConstructorAudit()
        );
        assertAuditError(
            audit => {
                audit.prerequisite.textRevision = 'stale';
            },
            'TEXT_DISPLAYED_CONSTRUCTOR_PREREQUISITE_DRIFT'
        );
        assertAuditError(
            audit => {
                audit.correctedResidualInventory
                    .genericApplicationAlreadyTextual[0].source =
                        'stale';
            },
            'TEXT_DISPLAYED_CONSTRUCTOR_INVENTORY_DRIFT'
        );
        assertAuditError(
            audit => {
                audit.proposal.operations[0].sourceName = 'stale';
            },
            'TEXT_DISPLAYED_CONSTRUCTOR_PROPOSAL_DRIFT'
        );
        assertAuditError(
            audit => {
                audit.semanticDelta.textResolverBranches = 1;
            },
            'TEXT_DISPLAYED_CONSTRUCTOR_BOUNDARY_DRIFT'
        );
    });
});
