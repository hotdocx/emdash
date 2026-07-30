/**
 * Focused executable SYNTAX-PARITY-1B2 independent-sibling audit tests.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_TEXT_SIBLING_AUDIT,
    CoreCategoricalProgram,
    CoreCategoricalTextSiblingAuditError,
    validateCoreCategoricalTextSiblingAudit
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
    CORE_CATEGORICAL_TEXT_SIBLING_AUDIT
));

const assertAuditError = (
    mutate: (audit: any) => void,
    code: CoreCategoricalTextSiblingAuditError['code']
): void => {
    const audit = cloneAudit();
    mutate(audit);
    assert.throws(
        () => validateCoreCategoricalTextSiblingAudit(audit),
        error =>
            error instanceof CoreCategoricalTextSiblingAuditError &&
            error.code === code
    );
};

const fixture = () => {
    const program = new CoreCategoricalProgram({
        sourceFile: 'tests/fixtures/categorical-text-sibling-audit.emdash',
        profile: 'fibred-displayed-bracket-1'
    });
    const K = program.category('K');
    const B = program.displayedFamily('B', K);
    const C = program.displayedFamily('C', K);
    const D = program.displayedFamily('D', K);
    const Q = program.displayedFamily('Q', K);
    const FF = program.displayedFunctor('FF', B, D);
    const GG = program.displayedFunctor('GG', C, Q);
    return {
        program,
        B,
        C,
        D,
        Q,
        FF,
        GG
    };
};

describe('SYNTAX-PARITY-1B2 independent-sibling text audit', () => {
    it('pins the exact pre-implementation parenthesized-binder seam', () => {
        assert.equal(
            CORE_CATEGORICAL_TEXT_SIBLING_AUDIT
                .prerequisite.textRevision,
            'SYNTAX-PARITY-1B1-CATEGORICAL-TEXT-1'
        );
        assert.deepEqual(
            CORE_CATEGORICAL_TEXT_SIBLING_AUDIT
                .measuredSeam.currentTextFailure,
            {
                phase: 'parsing',
                code: 'UNEXPECTED_TOKEN',
                startColumn: 6,
                endColumn: 7,
                detail: "Expected an identifier, found '('"
            }
        );
    });

    it('executes the existing direct sibling compiler and pairing owner',
        () => {
            const {
                program,
                B,
                C,
                D,
                Q,
                FF,
                GG
            } = fixture();
            const target = program.displayedProduct(D, Q);
            const direct = program.displayedContextLambda(
                [
                    { name: 'b', family: B },
                    { name: 'c', family: C }
                ],
                target,
                ([b, c]) => program.fibrePair(
                    program.apply(FF, b),
                    program.apply(GG, c)
                )
            );
            const compiled = program.compile(direct);
            const trace = compiled.abstractions.at(-1);
            assert.equal(
                trace?.rule,
                'categorical.displayed-context-bracket'
            );
            if (
                trace?.rule !==
                    'categorical.displayed-context-bracket'
            ) {
                assert.fail('Missing displayed sibling lowering trace');
            }
            assert.deepEqual(trace.bindingNames, ['b', 'c']);
            assert.equal(trace.contextRelation, 'shared-minimal-base-siblings');
            assert.equal(trace.body.tag, 'typed-pair');
            for (const prerequisite of [
                'displayed-product-left-projection',
                'displayed-product-right-projection',
                'generic-category-composition',
                'displayed-product-pair'
            ]) {
                assert.equal(
                    compiled.dependentPrerequisites.some(
                        candidate => candidate === prerequisite
                    ),
                    true
                );
            }
        });

    it('freezes comma siblings and reserves semicolons for 1B3', () => {
        const audit = CORE_CATEGORICAL_TEXT_SIBLING_AUDIT;
        assert.equal(
            audit.notationDecision.separatorMeaning.comma,
            'independent siblings at one dependency level'
        );
        assert.match(
            audit.notationDecision.separatorMeaning.semicolon,
            /SYNTAX-PARITY-1B3/u
        );
        assert.equal(
            audit.proposal.expectedContract.kind,
            'displayed-context-functor'
        );
        assert.deepEqual(
            audit.proposal.resolverDesign.operation,
            {
                sourceName: 'fibrePair',
                arity: 2,
                directMethod: 'fibrePair'
            }
        );
    });

    it('is deeply frozen, validates, and installs no behavior', () => {
        assertDeepFrozen(CORE_CATEGORICAL_TEXT_SIBLING_AUDIT);
        assert.doesNotThrow(
            () => validateCoreCategoricalTextSiblingAudit()
        );
        assert.equal(
            Object.values(
                CORE_CATEGORICAL_TEXT_SIBLING_AUDIT.semanticDelta
            ).some(value => value !== 0),
            false
        );
    });

    it('fails closed on prerequisite, measurement, notation, proposal, and boundary drift',
        () => {
            assertAuditError(
                audit => {
                    audit.prerequisite.textRevision = 'stale';
                },
                'TEXT_SIBLING_PREREQUISITE_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.measuredSeam.currentTextFailure.code = 'stale';
                },
                'TEXT_SIBLING_MEASUREMENT_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.notationDecision.separatorMeaning.comma =
                        'dependent';
                },
                'TEXT_SIBLING_NOTATION_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.proposal.resolverDesign.operation.arity = 1;
                },
                'TEXT_SIBLING_PROPOSAL_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.semanticDelta.textResolverBranches = 1;
                },
                'TEXT_SIBLING_BOUNDARY_DRIFT'
            );
        });
});
