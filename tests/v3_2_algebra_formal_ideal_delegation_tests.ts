/** Focused PCD-IDEAL-5B ideal-membership/quotient-equality tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    ALGEBRA_FORMAL_IDEAL_DELEGATION_PROFILE,
    AlgebraFormalDelegationError,
    RATIONAL_DOMAIN,
    adoptAlgebraFormalTrustedComputation,
    affineFormalCommRingType,
    affineFormalRingElementType,
    algebraFormalIdealEqualityDelegationBundle,
    algebraGroebnerBasis,
    algebraPolynomialAdd,
    algebraPolynomialIdeal,
    algebraPolynomialOne,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialVariable,
    algebraPolynomialZero,
    algebraPresentedAlgebra,
    coreProofPlanHole,
    createAffineFormalZariskiProofEnvironment,
    createAlgebraComputationGraphBuilder,
    createAlgebraFormalComputationRequest,
    createAlgebraTypeScriptReferenceEngine,
    createCoreProofArtifactFingerprint,
    defineAffineFormalPolynomialReifier,
    defineAlgebraFormalComputationGoal,
    defineAlgebraFormalIdealEqualityRealization,
    executeAlgebraComputationGraph,
    executeAlgebraFormalComputationRequest,
    kernelFree,
    provenance,
    serializeAlgebraFormalIdealMembership,
    serializeAlgebraFormalTrustedAdoptionArtifact
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);
const hex = (value: string): string => Array.from(new TextEncoder().encode(value))
    .map(byte => byte.toString(16).padStart(2, '0'))
    .join('');

const delegationError = (
    code: AlgebraFormalDelegationError['code']
): ((error: unknown) => boolean) => error => {
    assert.ok(error instanceof AlgebraFormalDelegationError);
    assert.equal(error.code, code);
    return true;
};

const fixture = (member: boolean) => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const one = algebraPolynomialOne(ring);
    const zero = algebraPolynomialZero(ring);
    const ideal = algebraPolynomialIdeal(ring, [x]);
    const basis = algebraGroebnerBasis(ideal);
    const left = member ? algebraPolynomialAdd(x, one) : one;
    const right = member ? one : zero;
    const quotient = algebraPolynomialQuotientRing(
        algebraPolynomialIdeal(ring, [])
    );
    const algebra = algebraPresentedAlgebra(quotient);
    const formalRing = kernelFree(
        member ? 'formal_ideal_positive_R' : 'formal_ideal_negative_R',
        because('formal ideal ring')
    );
    const formalX = kernelFree(
        member ? 'formal_ideal_positive_x' : 'formal_ideal_negative_x',
        because('formal ideal generator')
    );
    const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
    const reifier = defineAffineFormalPolynomialReifier({
        algebra,
        formalRing,
        generatorTerms: [formalX],
        coefficientReifier: coefficient => {
            const text = RATIONAL_DOMAIN.text(coefficient);
            const existing = coefficients.get(text);
            if (existing !== undefined) return existing;
            const term = kernelFree(
                `${member ? 'positive' : 'negative'}_coefficient_${hex(text)}`,
                because(`formal coefficient ${text}`)
            );
            coefficients.set(text, term);
            return term;
        },
        status: 'trusted-computation'
    });
    const realization = defineAlgebraFormalIdealEqualityRealization({
        basis,
        left,
        right,
        reifier
    });
    const elementType = affineFormalRingElementType(formalRing);
    const environment = createAffineFormalZariskiProofEnvironment([
        { name: formalRing.name, type: affineFormalCommRingType() },
        { name: formalX.name, type: elementType },
        ...[...coefficients.values()].map(term => ({
            name: term.name,
            type: elementType
        }))
    ]);
    const goalId = member ? 'positive-quotient-equality' :
        'negative-quotient-equality';
    const document = Object.freeze({
        moduleId: 'proof.cas.ideal',
        declarationId: member ? 'x_plus_one_equals_one' : 'one_equals_zero',
        environment,
        type: realization.claimType,
        plan: coreProofPlanHole(goalId, {
            provenance: because('ideal equality root hole'),
            expectation: {
                contextDepth: 0,
                target: realization.claimType
            }
        }),
        provenance: because('ideal equality proof root'),
        fingerprint: createCoreProofArtifactFingerprint({
            source: {
                id: `tests/fixtures/${goalId}.surface.ts`,
                sha256: `sha256:${member ? 'e'.repeat(64) : 'f'.repeat(64)}`
            },
            profileSha256: `sha256:${'1'.repeat(64)}`
        })
    });
    const goal = defineAlgebraFormalComputationGoal({ document, goalId });
    const bundle = algebraFormalIdealEqualityDelegationBundle(ring);
    const engine = createAlgebraTypeScriptReferenceEngine({
        id: member ? 'proof-cas.ideal-positive-reference' :
            'proof-cas.ideal-negative-reference',
        revision: 'v1',
        implementations: bundle.operations.implementations
    });
    return {
        ring,
        ideal,
        basis,
        realization,
        environment,
        document,
        goal,
        bundle,
        engine
    };
};

describe('PCD-IDEAL-5B ideal membership as formal quotient equality', () => {
    it('delegates x+1 = 1 modulo (x) and adopts the exact equality',
        async () => {
            const value = fixture(true);
            const request = createAlgebraFormalComputationRequest({
                adapter: value.bundle.adapter,
                goal: value.goal,
                realization: value.realization,
                engine: value.engine
            });
            const result = await executeAlgebraFormalComputationRequest(request);
            const adopted = adoptAlgebraFormalTrustedComputation({
                result,
                assumptionName: 'trusted_x_plus_one_equals_one',
                decision: {
                    kind: 'trust-exact-algebra-computation',
                    evidence: 'author trusts selected ideal relations and membership'
                }
            });
            const artifact =
                serializeAlgebraFormalTrustedAdoptionArtifact(adopted.artifact);

            assert.equal(result.computed.value.member, true);
            assert.equal(result.interpretation.kind, 'claim');
            assert.equal(result.interpretation.data.length, 1);
            assert.equal(adopted.execution.state.status, 'complete');
            assert.match(request.realizationData,
                /trusted-selected-ideal-relations/u);
            assert.match(artifact, /trusted_x_plus_one_equals_one/u);
            assert.equal(value.document.plan.tag, 'hole');
        }
    );

    it('retains the nonzero remainder for 1 != 0 modulo (x)', async () => {
        const value = fixture(false);
        const request = createAlgebraFormalComputationRequest({
            adapter: value.bundle.adapter,
            goal: value.goal,
            realization: value.realization,
            engine: value.engine
        });
        const result = await executeAlgebraFormalComputationRequest(request);

        assert.equal(result.computed.value.member, false);
        assert.equal(result.interpretation.kind, 'observation');
        assert.match(result.interpretation.summary, /remainder 1/u);
        assert.equal(value.document.plan.tag, 'hole');
        assert.throws(
            () => adoptAlgebraFormalTrustedComputation({
                result,
                assumptionName: 'invalid_one_equals_zero',
                decision: {
                    kind: 'trust-exact-algebra-computation',
                    evidence: 'negative membership must remain open'
                }
            }),
            delegationError('NO_ADOPTABLE_CLAIM')
        );
    });

    it('agrees with graph execution on the whole membership result',
        async () => {
            const value = fixture(true);
            const request = createAlgebraFormalComputationRequest({
                adapter: value.bundle.adapter,
                goal: value.goal,
                realization: value.realization,
                engine: value.engine
            });
            const direct = await executeAlgebraFormalComputationRequest(request);
            const builder = createAlgebraComputationGraphBuilder(
                'proof-cas.ideal-equality.graph',
                'v1'
            );
            const input = builder.input(
                'membership-input',
                value.bundle.operations.membershipInputSchema
            );
            const output = builder.operation(
                'membership',
                value.bundle.operations.membership,
                input
            );
            const graph = builder.build([{ id: 'result', value: output }]);
            const executed = await executeAlgebraComputationGraph({
                graph,
                engine: value.engine,
                inputs: [{
                    id: 'membership-input',
                    value: {
                        polynomial: value.realization.difference,
                        basis: value.basis
                    }
                }]
            });

            assert.equal(
                serializeAlgebraFormalIdealMembership(direct.computed.value),
                serializeAlgebraFormalIdealMembership(
                    executed.outputs[0].value as typeof direct.computed.value
                )
            );
        }
    );

    it('records the missing formal quotient rather than inventing one', () => {
        const value = fixture(true);
        assert.equal(
            value.realization.relationPolicy,
            'trusted-selected-ideal-relations'
        );
        assert.equal(
            ALGEBRA_FORMAL_IDEAL_DELEGATION_PROFILE.addsFormalQuotientOwner,
            false
        );
        assert.equal(ALGEBRA_FORMAL_IDEAL_DELEGATION_PROFILE.addsCoreOwner,
            false);
    });
});
