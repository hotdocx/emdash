/** Shared genuinely nonsplit examples for homology operations. */

import {
    RATIONAL_DOMAIN,
    algebraPolynomialFreeModule,
    algebraPolynomialFreydBoundedChainMap,
    algebraPolynomialFreydBoundedComplex,
    algebraPolynomialFreydCokernel,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialOne,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphismCongruence,
    algebraPolynomialPresentationMorphismZero,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPolynomialZero,
    algebraPresentedPolynomialModule
} from '../src/v3_2';
import { algebraPolynomialFreydBoundedShortExactSequence } from '../src/v3_2/algebra_polynomial_freyd_bounded_short_exact';
// All rows are R^r --x--> R^r → (R/(x))^r and are genuinely nonsplit.
export const polynomialFreydHomologyFixture = (shape: 'one' | 'two' | 'boundary' = 'two', variable = 'x') => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, [variable], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const z = algebraPolynomialZero(ring);
    const one = algebraPolynomialOne(ring);
    const ranks = shape === 'one' ? [1] : shape === 'two' ? [1, 1] : [1, 2, 1];
    const terms = ranks.map(rank => algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(algebraPolynomialFreeModule(ring, rank), [])
    ));
    const inclusions = terms.map(object => algebraPolynomialPresentationMorphism({
        source: object, target: object,
        map: algebraPolynomialModuleMap(object.ambient, object.ambient,
            Array.from({ length: object.ambient.rank }, (_, column) =>
                algebraPolynomialModuleVector(object.ambient,
                    Array.from({ length: object.ambient.rank }, (_, row) => row === column ? x : z)))
        )
    }));
    const quotients = inclusions.map(algebraPolynomialFreydCokernel);
    const differentials = shape === 'one' ? [] : [algebraPolynomialPresentationMorphism({
        source: terms[1], target: terms[0],
        map: algebraPolynomialModuleMap(terms[1].ambient, terms[0].ambient,
            shape === 'two' ? [algebraPolynomialModuleVector(terms[0].ambient, [x])] : [
                algebraPolynomialModuleVector(terms[0].ambient, [x]),
                algebraPolynomialModuleVector(terms[0].ambient, [z])
            ])
    })];
    if (shape === 'boundary') differentials.push(algebraPolynomialPresentationMorphism({
        source: terms[2], target: terms[1],
        map: algebraPolynomialModuleMap(terms[2].ambient, terms[1].ambient,
            [algebraPolynomialModuleVector(terms[1].ambient, [z, one])])
    }));
    const subcomplex = algebraPolynomialFreydBoundedComplex({ terms, differentials });
    const middleComplex = algebraPolynomialFreydBoundedComplex({ terms, differentials });
    const quotientComplex = algebraPolynomialFreydBoundedComplex({
        terms: quotients.map(value => value.object),
        differentials: differentials.map((value, index) => algebraPolynomialPresentationMorphism({
            source: quotients[index + 1].object,
            target: quotients[index].object,
            map: value.map
        }))
    });
    const inclusion = algebraPolynomialFreydBoundedChainMap({
        source: subcomplex, target: middleComplex, components: inclusions
    });
    const projection = algebraPolynomialFreydBoundedChainMap({
        source: middleComplex, target: quotientComplex,
        components: quotients.map(value => value.projection)
    });
    return algebraPolynomialFreydBoundedShortExactSequence({
        subcomplex, middleComplex, quotientComplex, inclusion, projection
    });
};

export const isPolynomialFreydMorphismZero = (map: ReturnType<typeof polynomialFreydHomologyFixture>['inclusion']['components'][number]['morphism']) =>
    algebraPolynomialPresentationMorphismCongruence(map,
        algebraPolynomialPresentationMorphismZero(map.source, map.target)).agrees;
