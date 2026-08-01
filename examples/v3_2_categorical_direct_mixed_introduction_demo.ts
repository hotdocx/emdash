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
const APrime = emdash.displayedFamily(
    'Demo_A_prime',
    emdash.oppositeCategory(K)
);
const B = emdash.displayedFamily('Demo_B', K);
const D = emdash.displayedFamily('Demo_D', K);
const functorFamily = emdash.mixedDisplayedFunctorFamily(A, B);
const F = emdash.displayedFunctor('Demo_F', C, functorFamily);
const G = emdash.displayedFunctor('Demo_G', B, D);
const L = emdash.displayedFunctor('Demo_L', APrime, A);

const directIdentity = emdash.mixedDisplayedFunctorLambda(
    { name: 'h', family: functorFamily },
    { name: 'a0', family: A },
    B,
    (h, a) => emdash.apply(h, a)
);
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
const sourceMapped = emdash.mixedDisplayedFunctorLambda(
    { name: 'c', family: C },
    { name: 'aPrime', family: APrime },
    D,
    (c, aPrime) => emdash.apply(
        G,
        emdash.apply(
            emdash.apply(F, c),
            emdash.apply(L, aPrime)
        )
    )
);
const directIdentityCompilation = emdash.compile(directIdentity);
const etaCompilation = emdash.compile(eta);
const mappedCompilation = emdash.compile(mapped);
const sourceMappedCompilation = emdash.compile(sourceMapped);
const evidence = emdash.inspect(mapped).abstractions.find(candidate =>
    candidate.rule ===
        'categorical.direct-mixed-displayed-functor'
);
const sourceEvidence = emdash.inspect(sourceMapped).abstractions.find(
    candidate => candidate.rule ===
        'categorical.direct-mixed-displayed-functor'
);

console.log(JSON.stringify({
    surface:
        'lambda^n k. lambda^f c. lambda^f a. G[k](F[k](c)(a))',
    sourceSurface:
        'lambda^n k. lambda^f c. lambda^f a\'. ' +
        'G[k](F[k](c)(L[k](a\')))',
    fundamentalIdentitySurface:
        'lambda^n k. lambda^f h. lambda^f a. h(a)',
    resultType: 'Functord C (Functor_catd A D)',
    fundamentalIdentityCore: directIdentityCompilation.explicitCore,
    etaCore: etaCompilation.explicitCore,
    mappedCore: mappedCompilation.explicitCore,
    sourceMappedCore: sourceMappedCompilation.explicitCore,
    sourceChainLength: sourceEvidence?.sourceChainLength,
    sourceThenTargetChainLength: sourceEvidence?.targetChainLength,
    targetChainLength: evidence?.targetChainLength,
    locallyNamelessBindings: evidence?.bindingNames,
    noContextualCurry:
        !mappedCompilation.explicitCore.includes('mixed_curry') &&
        !sourceMappedCompilation.explicitCore.includes('mixed_curry')
}, null, 2));
