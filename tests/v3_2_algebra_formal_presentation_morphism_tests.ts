/** Focused explicit-Core reification tests for presentation-map equations. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    RATIONAL_DOMAIN,
    affineFormalCommRingType,
    affineFormalRingElementType,
    algebraPolynomialChainMapSquare,
    algebraPolynomialFreeModule,
    algebraPolynomialIdeal,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialMultiply,
    algebraPolynomialOne,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphismAgreement,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPolynomialZero,
    algebraPresentedAlgebra,
    algebraPresentedPolynomialModule,
    createCoreProofChecker,
    createFormalPresentationMorphismProofEnvironment,
    defineAffineFormalPolynomialReifier,
    defineAlgebraFormalChainMapSquareRealization,
    defineAlgebraFormalPresentationAgreementRealization,
    defineAlgebraFormalPresentationMorphismRealization,
    kernelFree,
    kernelUniverse,
    provenance,
    serializeCoreExpression
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);

describe('FPMAP explicit-Core equation reification', () => {
    it('checks morphism, agreement, chain, and negative equation targets', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const zero = algebraPolynomialZero(ring);
        const one = algebraPolynomialOne(ring);
        const ambient = algebraPolynomialFreeModule(ring, 1);
        const source = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(ambient, [
                algebraPolynomialModuleVector(ambient, [x])
            ])
        );
        const target = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(ambient, [
                algebraPolynomialModuleVector(ambient, [x])
            ])
        );
        const stricterTarget = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(ambient, [
                algebraPolynomialModuleVector(ambient, [
                    algebraPolynomialMultiply(x, x)
                ])
            ])
        );
        const map = (polynomial: typeof x) => algebraPolynomialModuleMap(
            ambient,
            ambient,
            [algebraPolynomialModuleVector(ambient, [polynomial])]
        );
        const morphism = algebraPolynomialPresentationMorphism({
            source,
            target,
            map: map(y)
        });
        const negative = algebraPolynomialPresentationMorphism({
            source,
            target: stricterTarget,
            map: map(one)
        });
        const agreement = algebraPolynomialPresentationMorphismAgreement({
            source,
            target,
            left: map(x),
            right: map(zero)
        });
        const chain = algebraPolynomialChainMapSquare({
            differentialSource: map(x),
            differentialTarget: map(x),
            componentPrevious: map(y),
            componentNow: map(y)
        });
        const algebra = algebraPresentedAlgebra(
            algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))
        );
        const formalRing = kernelFree('formal_map_R', because('ring'));
        const formalX = kernelFree('formal_map_x', because('x'));
        const formalY = kernelFree('formal_map_y', because('y'));
        const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
        const reifier = defineAffineFormalPolynomialReifier({
            algebra,
            formalRing,
            generatorTerms: [formalX, formalY],
            coefficientReifier: coefficient => {
                const text = RATIONAL_DOMAIN.text(coefficient);
                let term = coefficients.get(text);
                if (term === undefined) {
                    const suffix = [...text].map(character =>
                        character.codePointAt(0)!.toString(16)
                    ).join('_');
                    term = kernelFree(
                        `formal_map_coefficient_${suffix}`,
                        because('coefficient')
                    );
                    coefficients.set(text, term);
                }
                return term;
            },
            status: 'trusted-computation'
        });
        const realizations = [
            defineAlgebraFormalPresentationMorphismRealization({
                reifier,
                selected: morphism
            }),
            defineAlgebraFormalPresentationMorphismRealization({
                reifier,
                selected: negative
            }),
            defineAlgebraFormalPresentationAgreementRealization({
                reifier,
                selected: agreement
            }),
            defineAlgebraFormalChainMapSquareRealization({
                reifier,
                selected: chain
            })
        ];
        const elementType = affineFormalRingElementType(formalRing);
        const environment = createFormalPresentationMorphismProofEnvironment([
            { name: formalRing.name, type: affineFormalCommRingType() },
            { name: formalX.name, type: elementType },
            { name: formalY.name, type: elementType },
            ...[...coefficients.values()].map(term => ({
                name: term.name,
                type: elementType
            }))
        ]);
        const checker = createCoreProofChecker(environment);
        checker.validateEnvironment();
        const universe = kernelUniverse(because('claim universe'));
        realizations.forEach(realization => checker.check(
            checker.rootContext,
            realization.claimType,
            universe
        ));

        assert.match(
            serializeCoreExpression(realizations[0].claimType),
            /bridge_comm_ring_matrix_comp/u
        );
        assert.match(
            serializeCoreExpression(realizations[2].claimType),
            /bridge_comm_ring_matrix_sub/u
        );
        assert.equal(morphism.preservesRelations, true);
        assert.equal(negative.preservesRelations, false);
        assert.equal(agreement.agrees, true);
        assert.equal(chain.commutes, true);
    });
});
