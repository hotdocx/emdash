/** Focused explicit-Core laws and recursive recipe tests for complexes. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    RATIONAL_DOMAIN,
    affineFormalCommRingType,
    affineFormalRingElementType,
    algebraPolynomialBoundedChainMap,
    algebraPolynomialBoundedFreeComplex,
    algebraPolynomialFreeModule,
    algebraPolynomialIdeal,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialVariable,
    algebraPolynomialZero,
    algebraPresentedAlgebra,
    createCoreProofChecker,
    createFormalPresentationMorphismProofEnvironment,
    defineAffineFormalPolynomialReifier,
    defineAlgebraFormalBoundedChainMapRealization,
    defineAlgebraFormalBoundedComplexRealization,
    kernelFree,
    kernelUniverse,
    provenance
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);

describe('FBC explicit-Core complex and chain-map laws', () => {
    it('reifies every law in recursive order and retains the whole recipe', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const zero = algebraPolynomialZero(ring);
        const module = algebraPolynomialFreeModule(ring, 1);
        const map = (value: typeof x) => algebraPolynomialModuleMap(
            module,
            module,
            [algebraPolynomialModuleVector(module, [value])]
        );
        const complex = algebraPolynomialBoundedFreeComplex({
            terms: [module, module, module],
            differentials: [map(x), map(zero)]
        });
        const chainMap = algebraPolynomialBoundedChainMap({
            source: complex,
            target: complex,
            components: [map(y), map(y), map(y)]
        });
        const algebra = algebraPresentedAlgebra(
            algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))
        );
        const formalRing = kernelFree('formal_complex_R', because('ring'));
        const formalX = kernelFree('formal_complex_x', because('x'));
        const formalY = kernelFree('formal_complex_y', because('y'));
        const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
        const reifier = defineAffineFormalPolynomialReifier({
            algebra,
            formalRing,
            generatorTerms: [formalX, formalY],
            coefficientReifier: coefficient => {
                const text = RATIONAL_DOMAIN.text(coefficient);
                let term = coefficients.get(text);
                if (term === undefined) {
                    term = kernelFree(
                        `formal_complex_coefficient_${text.replace('-', 'neg')}`,
                        because('coefficient')
                    );
                    coefficients.set(text, term);
                }
                return term;
            },
            status: 'trusted-computation'
        });
        const formalComplex = defineAlgebraFormalBoundedComplexRealization({
            reifier,
            selected: complex
        });
        const formalMap = defineAlgebraFormalBoundedChainMapRealization({
            reifier,
            selected: chainMap
        });
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
        const universe = kernelUniverse(because('law universe'));
        [
            ...formalComplex.conditions.map(condition => condition.claimType),
            ...formalMap.squares.map(square => square.claimType)
        ].forEach(claim => checker.check(checker.rootContext, claim, universe));

        assert.deepEqual(formalComplex.recipe.ranks, [1, 1, 1]);
        assert.equal(formalComplex.recipe.length, 2);
        assert.equal(formalComplex.recipe.lawTypes.length, 1);
        assert.equal(formalMap.formalComponents.length, 3);
        assert.equal(formalMap.squares.length, 2);
    });
});
