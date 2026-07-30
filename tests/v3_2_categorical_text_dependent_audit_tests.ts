/**
 * Focused executable SYNTAX-PARITY-1B3 dependent-context text audit tests.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_TEXT_DEPENDENT_AUDIT,
    CoreCategoricalProgram,
    CoreCategoricalTextDependentAuditError,
    validateCoreCategoricalTextDependentAudit
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
    CORE_CATEGORICAL_TEXT_DEPENDENT_AUDIT
));

const assertAuditError = (
    mutate: (audit: any) => void,
    code: CoreCategoricalTextDependentAuditError['code']
): void => {
    const audit = cloneAudit();
    mutate(audit);
    assert.throws(
        () => validateCoreCategoricalTextDependentAudit(audit),
        error =>
            error instanceof CoreCategoricalTextDependentAuditError &&
            error.code === code
    );
};

const fixture = () => {
    const program = new CoreCategoricalProgram({
        sourceFile:
            'tests/fixtures/categorical-text-dependent-audit.emdash',
        profile: 'fibred-displayed-chain-2a'
    });
    const K = program.category('dependent_audit_K');
    const A = program.displayedFamily('dependent_audit_A', K);
    const sigmaA = program.totalCategory(A);
    const B = program.displayedFamily('dependent_audit_B', sigmaA);
    const C = program.displayedFamily('dependent_audit_C', sigmaA);
    const P = program.displayedProduct(B, C);
    const sigmaP = program.totalCategory(P);
    const D = program.displayedFamily('dependent_audit_D', sigmaP);
    const projectionA = program.sigmaProjection(A);
    const liftedA = program.pullbackFamily(A, projectionA);
    const projectionP = program.sigmaProjection(P);
    const liftedB = program.pullbackFamily(B, projectionP);
    const liftedC = program.pullbackFamily(C, projectionP);
    const liftedProduct = program.displayedProduct(liftedB, liftedC);
    return {
        program,
        A,
        B,
        C,
        D,
        liftedA,
        liftedProduct
    };
};

describe('SYNTAX-PARITY-1B3 dependent-context text audit', () => {
    it('pins the exact pre-implementation semicolon parsing seam', () => {
        const audit = CORE_CATEGORICAL_TEXT_DEPENDENT_AUDIT;
        assert.equal(
            audit.prerequisite.textRevision,
            'SYNTAX-PARITY-1B2-CATEGORICAL-TEXT-1'
        );
        assert.deepEqual(audit.measuredSeam.currentTextFailure, {
            phase: 'parsing',
            code: 'UNEXPECTED_TOKEN',
            startColumn: 12,
            endColumn: 13,
            detail:
                'Semicolon dependency levels require the later ' +
                'SYNTAX-PARITY-1B3 profile'
        });
    });

    it('executes both existing direct dependent-context shapes', () => {
        const data = fixture();
        let callbacks = 0;
        const edge =
            data.program.displayedDependentContextLambda(
                [
                    { name: 'a', family: data.A },
                    { name: 'b', family: data.B }
                ],
                data.liftedA,
                ([a]) => {
                    callbacks += 1;
                    return a;
                }
            );
        const mixed =
            data.program.displayedDependentContextLambda(
                [
                    { name: 'a', family: data.A },
                    { name: 'b', family: data.B },
                    { name: 'c', family: data.C },
                    { name: 'd', family: data.D }
                ],
                data.liftedProduct,
                ([, b, c]) => {
                    callbacks += 1;
                    return data.program.fibrePair(b, c);
                }
            );
        assert.equal(callbacks, 2);

        const edgeTrace =
            data.program.compile(edge).abstractions.at(-1);
        assert.equal(
            edgeTrace?.rule,
            'categorical.displayed-dependent-context-bracket'
        );
        if (
            edgeTrace?.rule !==
                'categorical.displayed-dependent-context-bracket'
        ) {
            assert.fail('Missing genuine-edge lowering trace');
        }
        assert.deepEqual(edgeTrace.bindingNames, ['a', 'b']);
        assert.equal(
            edgeTrace.contextRelation,
            'one-genuine-dependency-edge'
        );

        const mixedCompilation = data.program.compile(mixed);
        const mixedTrace = mixedCompilation.abstractions.at(-1);
        assert.equal(
            mixedTrace?.rule,
            'categorical.displayed-mixed-dependent-context-bracket'
        );
        if (
            mixedTrace?.rule !==
                'categorical.displayed-mixed-dependent-context-bracket'
        ) {
            assert.fail('Missing mixed-telescope lowering trace');
        }
        assert.deepEqual(
            mixedTrace.bindingNames,
            ['a', 'b', 'c', 'd']
        );
        assert.deepEqual(mixedTrace.siblingGroup, ['b', 'c']);
        assert.equal(
            mixedTrace.contextRelation,
            'two-dependency-transitions-with-middle-siblings'
        );
        assert.equal(mixedTrace.body.tag, 'typed-pair');
        assert.match(
            mixedCompilation.explicitCore,
            /emdash\.categorical\.displayed-product-pair/u
        );
    });

    it('freezes exact semicolon levels and bounded direct shapes', () => {
        const audit = CORE_CATEGORICAL_TEXT_DEPENDENT_AUDIT;
        assert.deepEqual(
            audit.measuredSeam.exactDirectShapes.map(
                shape => shape.groupSizes
            ),
            [[1, 1], [1, 2, 1]]
        );
        assert.equal(
            audit.notationDecision.separatorMeaning.semicolon,
            'successive displayed dependency levels'
        );
        assert.equal(
            audit.proposal.expectedContract.kind,
            'displayed-dependent-context-functor'
        );
        assert.equal(
            audit.proposal.resolverDesign.abstractionMethod,
            'displayedDependentContextLambda'
        );
        assert.equal(
            audit.proposal.reviewerPreset.id,
            'displayed-mixed-telescope'
        );
    });

    it('is deeply frozen, validates, and installs no behavior', () => {
        assertDeepFrozen(CORE_CATEGORICAL_TEXT_DEPENDENT_AUDIT);
        assert.doesNotThrow(
            () => validateCoreCategoricalTextDependentAudit()
        );
        assert.equal(
            Object.values(
                CORE_CATEGORICAL_TEXT_DEPENDENT_AUDIT.semanticDelta
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
                'TEXT_DEPENDENT_PREREQUISITE_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.measuredSeam.exactDirectShapes[0]
                        .groupSizes = [2];
                },
                'TEXT_DEPENDENT_MEASUREMENT_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.notationDecision.separatorMeaning.semicolon =
                        'siblings';
                },
                'TEXT_DEPENDENT_NOTATION_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.proposal.expectedContract.kind = 'stale';
                },
                'TEXT_DEPENDENT_PROPOSAL_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.semanticDelta.coreOwners = 1;
                },
                'TEXT_DEPENDENT_BOUNDARY_DRIFT'
            );
        });
});
