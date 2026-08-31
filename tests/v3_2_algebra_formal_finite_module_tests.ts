/** Focused formal finite-module reification tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    RATIONAL_DOMAIN,
    algebraFormalModuleMembershipBundle,
    algebraPolynomialFreeModule,
    algebraPolynomialIdeal,
    algebraPolynomialModuleGroebnerBasis,
    algebraPolynomialModuleMembership,
    algebraPolynomialModuleVector,
    algebraPolynomialOne,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialVariable,
    algebraPolynomialSubmodule,
    algebraPresentedAlgebra,
    createAlgebraTypeScriptReferenceEngine,
    defineAffineFormalPolynomialReifier,
    defineAlgebraFormalModuleMembershipRealization,
    computeAlgebraOperation,
    kernelFree,
    provenance,
    serializeCoreExpression
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);

describe('FPM-REIFY membership representation', () => {
    it('reifies a selected one-generator module membership equation',
        async () => {
            const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
            const x = algebraPolynomialVariable(ring, 0);
            const module = algebraPolynomialFreeModule(ring, 1);
            const generator = algebraPolynomialModuleVector(module, [x]);
            const basis = algebraPolynomialModuleGroebnerBasis(
                algebraPolynomialSubmodule(module, [generator])
            );
            const selected = algebraPolynomialModuleMembership(generator, basis);
            const algebra = algebraPresentedAlgebra(
                algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))
            );
            const reifier = defineAffineFormalPolynomialReifier({
                algebra,
                formalRing: kernelFree('formal_module_R', because('ring')),
                generatorTerms: [kernelFree('formal_module_x', because('x'))],
                coefficientReifier: coefficient => kernelFree(
                    `formal_module_coefficient_${RATIONAL_DOMAIN.text(coefficient)}`,
                    because('coefficient')
                ),
                status: 'trusted-computation'
            });
            const realization = defineAlgebraFormalModuleMembershipRealization({
                reifier,
                vector: generator,
                basis,
                selected
            });
            const core = serializeCoreExpression(realization.claimType);
            assert.match(core, /bridge_comm_ring_matrix_apply/u);
            assert.match(core, /bridge_CommRingVector/u);
            assert.equal(selected.member, true);

            const bundle = algebraFormalModuleMembershipBundle(generator);
            const engine = createAlgebraTypeScriptReferenceEngine({
                implementations: bundle.implementations
            });
            const computed = await computeAlgebraOperation({
                engine,
                operation: bundle.operation,
                input: realization.input
            });
            assert.equal(computed.value.member, true);

            const negative = algebraPolynomialModuleVector(module, [
                algebraPolynomialOne(ring)
            ]);
            assert.equal(
                algebraPolynomialModuleMembership(negative, basis).member,
                false
            );
        }
    );
});
