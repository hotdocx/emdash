Your intuition about the computational owner is right, but the precise internal type must be one level weaker than a global `CoreIncl_ : Core ⇒ Id_Cat`.

The immediate construction should be:

```text
Core₀(C) ≔ Path_cat(Obj(C))

Core₁(F) ≔ PathMap(F₀)
  : Core₀(C) → Core₀(D)

ι_C ≔ Core_incl_func(C)
  : Core₀(C) → C

κ_F :
  F ∘ ι_C
    ⇒
  ι_D ∘ Core₁(F).
```

Its computations are determined by path induction:

```text
κ_F[x] ↪ id_(F(x))

F(path_to_hom_C(p))
  = path_to_hom_D(eq_ap(F₀,p)).
```

Thus `κ_F` is the internally packaged naturality cell of Core inclusion along a fixed functor `F`. Whiskering by `G` gives exactly:

```text
κ_F ⋆ G :
  F ∘ hom_postcomp(ι_C,G)
    ⇒
  hom_postcomp(ι_D,PathMap(F₀) ∘ G).
```

There are two legitimate computational representations to probe:

1. Construct `κ_F` transparently using existing equality/PathOut machinery and give it the full `tapp*` ladder.
2. Make Core inclusion strictly natural by selecting:

```text
F ∘ ι_C
  ↪ ι_D ∘ PathMap(F₀),
```

so `κ_F` becomes the ordinary identity transfor. Its stable `hom_postcomp` accumulation then follows as the consumer-level projection rule you proposed.

The second may ultimately be the cleaner computational design, but it must be tested first at the smaller `F ∘ ι_C` owner. No bodyless `κ_F`, HIT-specific rule, or five probe-local `unif_rule`s should remain.

Two important clarifications:

- `Core_cat(C)` being a transparent alias is not itself the obstacle. It correctly defines only the object-level assignment. Making it `injective` would not manufacture functor, transfor, and higher-cell actions.
- The current `Core_incl_func(C)` sends paths to arrows. Collapsing arbitrary arrows back to paths is its inverse and requires `IsGroupoidalCat(C)` or `IsDiscreteCat(C)` evidence. A literal global `Core : Functor Cat_cat Cat_cat` would have to turn every component `ηₓ : F(x) → G(x)` into a path `F(x)=G(x)`, which is unavailable for general directed categories.

For WalkingEnd that distinction is essential: globally collapsing its generating arrow would groupoid-complete the free monoid, changing the intended ℕ behavior toward ℤ.

Accordingly, the actual semantic definition remains:

```text
PathLift_A,C
  ≔ comp_cat_cov_func(ι_C)
       ∘ PathInt₁(A,Obj(C)).
```

It is not literally `tapp1_func(CoreIncl_)` under the current types. The new `κ_F`/strict-CoreIncl owner supplies exactly the naturality computation that `PathLift` needs.

I updated the [walking-endomorphism plan](/home/user1/emdash1/emdash2/reports/REPORT_EMDASH_V3_2_WALKING_ENDOMORPHISM_DIRECTED_HIT_PLAN_2026-07-17.md) with this focused gate. `git diff --check` passes; no kernel files were changed.