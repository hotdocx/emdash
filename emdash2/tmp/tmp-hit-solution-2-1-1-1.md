The computations support your alternative: a primitive `PathLift` is not yet justified. Most of the desired behavior already follows by unfolding its semantic definition and using existing owners.

The computed normal forms are:

```text
F ∘ PathLift(f)

↪ F ∘ hom_postcomp(CoreIncl_C, PathMap(f))
```

and then it stops.

But:

```text
PathLift(f) ∘ PathMap(g)

↪ hom_postcomp(CoreIncl_C, PathMap(f ∘ g))
≡ PathLift(f ∘ g).
```

The computed desired RHS is literally the same normal form. Without the experimental global `Grpd` composition rewrite, it remains:

```text
hom_postcomp(CoreIncl_C, PathMap(comp_Grpd(f,g))),
```

which is still structurally the correct `PathLift(f ∘ g)` presentation.

So only the postcomposition direction is genuinely missing. The likely generic rule belongs to the existing `CoreIncl`/`hom_postcomp_fapp0` owner:

```text
F ∘ hom_postcomp(CoreIncl_C,G)
  ↪
hom_postcomp(
  CoreIncl_D,
  PathMap(F₀) ∘ G).
```

Specializing `G ≔ PathMap(f)` then gives:

```text
F ∘ PathLift(f)
  ↪ hom_postcomp(CoreIncl_D,PathMap(F₀) ∘ PathMap(f))
  ↪ hom_postcomp(CoreIncl_D,PathMap(F₀ ∘ f))
  ≡ PathLift(F₀ ∘ f).
```

This is preferable to a PathLift-specific rule because it expresses the more general semantic fact:

```text
F ∘ CoreIncl_C
  ↪ CoreIncl_D ∘ PathMap(F₀)
```

under the existing stable postcomposition owner. It also keeps the resulting functor visible and iterable.

There remains a separate lower-level issue:

```text
comp_Grpd(f,g)
```

versus the executable pointwise head:

```text
grpd_comp_function(f,g).
```

That is a general internal function-composition computation issue, not a `PathLift` issue. We should not hide it using PathLift-specific unification rules.

Therefore the next minimal probe should:

1. give `PathInt`/`PathMap`/`PathTransf` a proper named projection ladder;
2. retain transparent:

   ```text
   PathLift_sem ≔ hom_postcomp(CoreIncl,PathMap(−));
   ```

3. add only the generic Core-inclusion/postcomposition accumulation above;
4. remove the five probe-specific `unif_rule`s;
5. use the ordinary categorical `comp_Grpd` presentation initially;
6. test exact spiral formation, component computation, and full higher action.

Only if the transparent body still loses a head required by a real consumer should we introduce a primitive stable `PathLift`. The current normalization evidence says the existing `hom_postcomp_fapp0` head may already be the stable intermediary we need.