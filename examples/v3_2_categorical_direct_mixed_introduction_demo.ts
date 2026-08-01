/**
 * Runnable direct mixed-introduction demo.
 *
 * Run from the repository root with:
 *
 *   ./scripts/pnpmw run demo:categorical-direct-mixed-introduction
 */

import assert from 'node:assert/strict';
import {
    CoreCategoricalProgram,
    coreCategoricalDirectMixedWeakeningCoreName
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
const H = emdash.displayedFunctor('Demo_H', C, B);

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
const innerWeakened = emdash.mixedDisplayedFunctorLambda(
    { name: 'cWeak', family: C },
    { name: 'aUnused', family: A },
    B,
    (c, _a) => emdash.apply(H, c)
);
const mappedInnerWeakened = emdash.mixedDisplayedFunctorLambda(
    { name: 'cWeakMapped', family: C },
    { name: 'aUnusedMapped', family: A },
    D,
    (c, _a) => emdash.apply(G, emdash.apply(H, c))
);
const directIdentityCompilation = emdash.compile(directIdentity);
const etaCompilation = emdash.compile(eta);
const mappedCompilation = emdash.compile(mapped);
const sourceMappedCompilation = emdash.compile(sourceMapped);
const innerWeakenedCompilation = emdash.compile(innerWeakened);
const mappedInnerWeakenedCompilation = emdash.compile(
    mappedInnerWeakened
);
const evidence = emdash.inspect(mapped).abstractions.find(candidate =>
    candidate.rule ===
        'categorical.direct-mixed-displayed-functor'
);
const sourceEvidence = emdash.inspect(sourceMapped).abstractions.find(
    candidate => candidate.rule ===
        'categorical.direct-mixed-displayed-functor'
);
const weakeningEvidence = emdash.inspect(innerWeakened).abstractions.find(
    candidate => candidate.rule ===
        'categorical.direct-mixed-displayed-functor'
);
const weakeningCoreName = coreCategoricalDirectMixedWeakeningCoreName(
    'weakening'
);

assert.match(innerWeakenedCompilation.explicitCore, new RegExp(
    weakeningCoreName,
    'u'
));
assert.equal(weakeningEvidence?.rootKind, 'outer-value-weakening');
assert.equal(weakeningEvidence?.innerUsageCount, 0);
assert.doesNotMatch(
    mappedInnerWeakenedCompilation.explicitCore,
    /mixed_curry|mix_uncurried_family|coerc|cast/u
);

console.log(JSON.stringify({
    surface:
        'lambda^n k. lambda^f c. lambda^f a. G[k](F[k](c)(a))',
    sourceSurface:
        'lambda^n k. lambda^f c. lambda^f a\'. ' +
        'G[k](F[k](c)(L[k](a\')))',
    fundamentalIdentitySurface:
        'lambda^n k. lambda^f h. lambda^f a. h(a)',
    innerWeakeningSurface:
        'lambda^n k. lambda^f c. lambda^f a. H[k](c)',
    resultType: 'Functord C (Functor_catd A D)',
    fundamentalIdentityCore: directIdentityCompilation.explicitCore,
    etaCore: etaCompilation.explicitCore,
    mappedCore: mappedCompilation.explicitCore,
    sourceMappedCore: sourceMappedCompilation.explicitCore,
    innerWeakenedCore: innerWeakenedCompilation.explicitCore,
    mappedInnerWeakenedCore:
        mappedInnerWeakenedCompilation.explicitCore,
    innerWeakeningRootKind: weakeningEvidence?.rootKind,
    innerWeakeningOuterUses: weakeningEvidence?.outerUsageCount,
    innerWeakeningInnerUses: weakeningEvidence?.innerUsageCount,
    sourceChainLength: sourceEvidence?.sourceChainLength,
    sourceThenTargetChainLength: sourceEvidence?.targetChainLength,
    targetChainLength: evidence?.targetChainLength,
    locallyNamelessBindings: evidence?.bindingNames,
    noContextualCurry:
        !mappedCompilation.explicitCore.includes('mixed_curry') &&
        !sourceMappedCompilation.explicitCore.includes('mixed_curry') &&
        !mappedInnerWeakenedCompilation.explicitCore.includes(
            'mixed_curry'
        )
}, null, 2));
