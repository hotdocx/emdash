/** Focused CAS-HOMOLOGICAL-7A4 generalized-span tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    algebraMatrix,
    algebraMatrixSpace,
    algebraZeroMatrix
} from '../src/v3_2/algebra_matrix';
import {
    algebraFreeModule,
    algebraModuleCompose,
    algebraModuleIdentity,
    algebraModuleInducedMatrix,
    algebraModuleMorphism,
    algebraModuleMorphismEquivalent,
    algebraModuleZeroMorphism
} from '../src/v3_2/algebra_module';
import {
    ALGEBRA_GENERALIZED_MORPHISM_PROFILE,
    AlgebraGeneralizedMorphismError,
    algebraModuleAsGeneralizedSpan,
    algebraModuleGeneralizedSpan,
    algebraModuleGeneralizedSpanComposition,
    algebraModuleGeneralizedSpanHonestRepresentative,
    algebraModuleGeneralizedSpanIdentity,
    algebraModulePullback,
    algebraModulePullbackLift
} from '../src/v3_2/algebra_generalized';

const generalizedError = (code: AlgebraGeneralizedMorphismError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraGeneralizedMorphismError);
        assert.equal(error.code, code);
        return true;
    };

const zeroWitness = () => algebraZeroMatrix(algebraMatrixSpace(
    RATIONAL_DOMAIN,
    0,
    0
));

describe('v3.2 generalized field-module morphisms by spans', () => {
    it('computes a module pullback and its universal lift', () => {
        const leftSource = algebraFreeModule(RATIONAL_DOMAIN, 2);
        const rightSource = algebraFreeModule(RATIONAL_DOMAIN, 1);
        const target = algebraFreeModule(RATIONAL_DOMAIN, 1);
        const left = algebraModuleMorphism(
            leftSource,
            target,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 1, 2),
                [['1', '0']]
            ),
            zeroWitness()
        );
        const right = algebraModuleIdentity(rightSource);
        const pullback = algebraModulePullback(left, right);
        assert.equal(pullback.object.generators, 2);
        assert.ok(algebraModuleMorphismEquivalent(
            algebraModuleCompose(left, pullback.leftProjection),
            algebraModuleCompose(right, pullback.rightProjection)
        ));

        const testSource = algebraFreeModule(RATIONAL_DOMAIN, 1);
        const testLeft = algebraModuleMorphism(
            testSource,
            leftSource,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 2, 1),
                [['2'], ['3']]
            ),
            zeroWitness()
        );
        const testRight = algebraModuleMorphism(
            testSource,
            rightSource,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 1, 1),
                [['2']]
            ),
            zeroWitness()
        );
        const lift = algebraModulePullbackLift(
            pullback,
            testLeft,
            testRight
        );
        assert.ok(algebraModuleMorphismEquivalent(
            algebraModuleCompose(pullback.leftProjection, lift),
            testLeft
        ));
        assert.ok(algebraModuleMorphismEquivalent(
            algebraModuleCompose(pullback.rightProjection, lift),
            testRight
        ));
        const badRight = algebraModuleMorphism(
            testSource,
            rightSource,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 1, 1),
                [['3']]
            ),
            zeroWitness()
        );
        assert.throws(
            () => algebraModulePullbackLift(pullback, testLeft, badRight),
            generalizedError('PULLBACK_CONDITION_FAILED')
        );
    });

    it('embeds honest maps and composes them through a retained pullback', () => {
        const source = algebraFreeModule(RATIONAL_DOMAIN, 2);
        const middle = algebraFreeModule(RATIONAL_DOMAIN, 1);
        const target = algebraFreeModule(RATIONAL_DOMAIN, 1);
        const first = algebraModuleMorphism(
            source,
            middle,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 1, 2),
                [['1', '2']]
            ),
            zeroWitness()
        );
        const second = algebraModuleMorphism(
            middle,
            target,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 1, 1),
                [['3']]
            ),
            zeroWitness()
        );
        const firstGeneralized = algebraModuleAsGeneralizedSpan(first);
        const secondGeneralized = algebraModuleAsGeneralizedSpan(second);
        const composition = algebraModuleGeneralizedSpanComposition(
            secondGeneralized,
            firstGeneralized
        );
        const representative =
            algebraModuleGeneralizedSpanHonestRepresentative(
                composition.result
            );
        assert.ok(algebraModuleMorphismEquivalent(
            representative,
            algebraModuleCompose(second, first)
        ));
        assert.deepEqual(
            algebraModuleInducedMatrix(representative).entries.map(row =>
                row.map(RATIONAL_DOMAIN.text)
            ),
            [['3', '6']]
        );
        const identity = algebraModuleGeneralizedSpanIdentity(source);
        const identityComposition = algebraModuleGeneralizedSpanComposition(
            firstGeneralized,
            identity
        );
        assert.ok(algebraModuleMorphismEquivalent(
            algebraModuleGeneralizedSpanHonestRepresentative(
                identityComposition.result
            ),
            first
        ));
        assert.ok(Object.isFrozen(composition));
        assert.ok(Object.isFrozen(composition.pullback));
    });

    it('retains partial domains and rejects unsupported or invalid spans', () => {
        const source = algebraFreeModule(RATIONAL_DOMAIN, 2);
        const domain = algebraFreeModule(RATIONAL_DOMAIN, 1);
        const target = algebraFreeModule(RATIONAL_DOMAIN, 1);
        const sourceAid = algebraModuleMorphism(
            domain,
            source,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 2, 1),
                [['1'], ['0']]
            ),
            zeroWitness()
        );
        const partial = algebraModuleGeneralizedSpan(
            sourceAid,
            algebraModuleIdentity(domain)
        );
        const twice = algebraModuleAsGeneralizedSpan(algebraModuleMorphism(
            target,
            target,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 1, 1),
                [['2']]
            ),
            zeroWitness()
        ));
        const partialComposite = algebraModuleGeneralizedSpanComposition(
            twice,
            partial
        );
        assert.equal(partialComposite.result.domain.generators, 1);
        assert.equal(
            RATIONAL_DOMAIN.text(
                algebraModuleInducedMatrix(
                    partialComposite.result.arrow
                ).entries[0][0]
            ),
            '2'
        );
        assert.throws(
            () => algebraModuleGeneralizedSpanHonestRepresentative(partial),
            generalizedError('NO_HONEST_REPRESENTATIVE')
        );
        assert.throws(
            () => algebraModuleGeneralizedSpan(
                algebraModuleZeroMorphism(domain, target),
                algebraModuleIdentity(domain)
            ),
            generalizedError('NON_MONIC_SOURCE_AID')
        );
        assert.throws(
            () => algebraModuleGeneralizedSpanComposition(
                algebraModuleGeneralizedSpanIdentity(source),
                partial
            ),
            generalizedError('NON_COMPOSABLE_GENERALIZED_SPANS')
        );
        assert.equal(
            ALGEBRA_GENERALIZED_MORPHISM_PROFILE.threeArrowRepresentation,
            false
        );
        assert.equal(
            ALGEBRA_GENERALIZED_MORPHISM_PROFILE.serreQuotients,
            false
        );
    });
});
