/**
 * Runnable direct mixed-introduction demo.
 *
 * Run from the repository root with:
 *
 *   ./scripts/pnpmw run demo:categorical-direct-mixed-introduction
 */

import {
    CoreCategoricalProgram
} from '../src/v3_2';

const emdash = new CoreCategoricalProgram({
    sourceFile: 'examples/v3_2_categorical_direct_mixed_introduction_demo.ts',
    profile: 'fibred-direct-mixed-introduction-1'
});
const K = emdash.category('Demo_K');
const C = emdash.displayedFamily('Demo_C', K);
const A = emdash.displayedFamily(
    'Demo_A',
    emdash.oppositeCategory(K)
);
const B = emdash.displayedFamily('Demo_B', K);
const D = emdash.displayedFamily('Demo_D', K);
const functorFamily = emdash.mixedDisplayedFunctorFamily(A, B);
const F = emdash.displayedFunctor('Demo_F', C, functorFamily);
const G = emdash.displayedFunctor('Demo_G', B, D);

const eta = emdash.mixedDisplayedFunctorLambda(
    { name: 'c', family: C },
    { name: 'a', family: A },
    B,
    (c, a) => emdash.apply(emdash.apply(F, c), a)
);
const mapped = emdash.mixedDisplayedFunctorLambda(
    { name: 'c', family: C },
    { name: 'a', family: A },
    D,
    (c, a) => emdash.apply(
        G,
        emdash.apply(emdash.apply(F, c), a)
    )
);
const etaCompilation = emdash.compile(eta);
const mappedCompilation = emdash.compile(mapped);
const evidence = emdash.inspect(mapped).abstractions.find(candidate =>
    candidate.rule ===
        'categorical.direct-mixed-displayed-functor'
);

console.log(JSON.stringify({
    surface:
        'lambda^n k. lambda^f c. lambda^f a. G[k](F[k](c)(a))',
    resultType: 'Functord C (Functor_catd A D)',
    etaCore: etaCompilation.explicitCore,
    mappedCore: mappedCompilation.explicitCore,
    targetChainLength: evidence?.targetChainLength,
    locallyNamelessBindings: evidence?.bindingNames,
    noContextualCurry:
        !mappedCompilation.explicitCore.includes('mixed_curry')
}, null, 2));
