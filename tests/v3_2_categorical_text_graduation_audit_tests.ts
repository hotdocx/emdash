/**
 * Focused executable post-1C3 syntax-graduation audit tests.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_TEXT_GRADUATION_AUDIT,
    CORE_CATEGORICAL_TEXT_PARITY_AUDIT,
    CoreCategoricalProgram,
    CoreCategoricalTextError,
    CoreCategoricalTextGraduationAuditError,
    elaborateCoreCategoricalText,
    validateCoreCategoricalTextGraduationAudit
} from '../src/v3_2';

const sourceFile =
    'tests/fixtures/categorical-text-graduation-audit.emdash';

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
    CORE_CATEGORICAL_TEXT_GRADUATION_AUDIT
));

const program = new CoreCategoricalProgram({ sourceFile });
const A = program.category('graduate_A');
const B = program.category('graduate_B');
const C = program.category('graduate_C');
const functorsBC = program.functorCategory(B, C);
const functorsAC = program.functorCategory(A, C);
const E = program.functor('graduate_E', B, functorsAC);

describe('SYNTAX-PARITY-GRADUATE-0A audit', () => {
    it('partitions the original 68-method surface exactly', () => {
        const audit = CORE_CATEGORICAL_TEXT_GRADUATION_AUDIT;
        const originalMethods =
            CORE_CATEGORICAL_TEXT_PARITY_AUDIT.capabilities.flatMap(
                capability => capability.apiMethods
            );
        const host = Object.values(
            audit.publicMethodClassification.deliberatelyHostSide
        ).flat();
        const originalSet = new Set<string>(originalMethods);
        const hostSet = new Set<string>(host);
        assert.equal(originalMethods.length, 68);
        assert.equal(originalSet.size, 68);
        assert.equal(host.length, 21);
        assert.equal(hostSet.size, 21);
        host.forEach(method =>
            assert.equal(originalSet.has(method), true)
        );
        assert.equal(
            originalMethods.filter(method => !hostSet.has(method)).length,
            47
        );
        assert.equal(
            audit.currentTextEnvelope.operationHeads.length,
            37
        );
    });

    it('measures one direct-green nested ordinary text gap', () => {
        const direct = program.lambda(
            'x',
            A,
            functorsBC,
            x => program.lambda(
                'y',
                B,
                C,
                y => program.apply(
                    program.apply(E, y),
                    x
                )
            )
        );
        assert.equal(program.compile(direct).surfaceType.tag, 'functor');

        assert.throws(
            () => elaborateCoreCategoricalText(program, {
                source: 'λ^f x : A. λ^f y : B. E y x',
                sourceFile,
                environment: [
                    { name: 'A', kind: 'category', value: A },
                    { name: 'B', kind: 'category', value: B },
                    { name: 'E', kind: 'term', value: E }
                ],
                expected: {
                    kind: 'ordinary-functor',
                    source: A,
                    target: functorsBC
                }
            }),
            error =>
                error instanceof CoreCategoricalTextError &&
                error.code === 'UNSUPPORTED_NESTED_ABSTRACTION' &&
                error.span.start.column === 12
        );
    });

    it('separates optional presentation sugar from semantic boundaries',
        () => {
            const audit = CORE_CATEGORICAL_TEXT_GRADUATION_AUDIT;
            assert.deepEqual(
                audit.nonBlockingResiduals.map(entry =>
                    entry.classification
                ),
                [
                    'optional-presentation-convenience',
                    'direct-semantic-capability-boundary',
                    'direct-semantic-capability-boundary',
                    'unreviewed-direct-semantic-boundary'
                ]
            );
            assert.equal(
                audit.publicMethodClassification
                    .normalizedAliases[0].canonicalTextHead,
                'pullback'
            );
            assert.equal(
                audit.status,
                'graduation-blocked-by-one-measured-parser-gap'
            );
        });

    it('is deeply frozen, validates, and fails closed on drift', () => {
        const audit = CORE_CATEGORICAL_TEXT_GRADUATION_AUDIT;
        assertDeepFrozen(audit);
        assert.doesNotThrow(
            () => validateCoreCategoricalTextGraduationAudit()
        );

        const gapDrift = cloneAudit();
        gapDrift.blockingGap.currentFailure.code = 'changed';
        assert.throws(
            () => validateCoreCategoricalTextGraduationAudit(gapDrift),
            error =>
                error instanceof CoreCategoricalTextGraduationAuditError &&
                error.code === 'GRADUATION_GAP_DRIFT'
        );

        const hostDrift = cloneAudit();
        hostDrift.publicMethodClassification
            .deliberatelyHostSide.observations.pop();
        assert.throws(
            () => validateCoreCategoricalTextGraduationAudit(hostDrift),
            error =>
                error instanceof CoreCategoricalTextGraduationAuditError &&
                error.code === 'GRADUATION_HOST_CLASSIFICATION_DRIFT'
        );
    });
});
