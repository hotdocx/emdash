# Plan Draft: v3 Foundations, Internal Functoriality, and Sigma Hom

## Summary

This report has been revised after the `Fam/Core` review. The current source of truth is no longer the older `Catd`-first plan below. The corrected v3 foundation should introduce a general directed family layer:

```text
Fam_cat (K : Cat) : Cat
  := Functor_cat K Cat_cat

Fam (K : Cat) : Grpd
  := Obj (Fam_cat K)
```

and then treat core displayed categories as the HoTT/path-specialized instance:

```text
Catd_cat (Z : Cat) : Cat
  := Fam_cat (Core_cat Z)

Catd (Z : Cat) : TYPE
  := τ (Fam (Core_cat Z))
```

Under this revision, core restriction and Grothendieck/Sigma totalization are separate operations:

```text
core restriction:
  M : τ (Fam K)
  M|core := M ∘ Core_incl_func K : τ (Fam (Core_cat K))

Grothendieck / dependent sum:
  Sigma_cat M : Cat
  Sigma_proj1_func M : τ (Functor (Sigma_cat M) K)
```

The old intuition that `Fibration_cov_catd M` is "the Grothendieck construction" is now superseded. In the new architecture, `Fibration_cov_catd M` is only a compatibility name for restriction of `M : τ (Fam Z)` along `Core_incl_func Z`. The actual total category preserving directed base-arrow data is `Sigma_cat M`.

The earlier `tmp-2007.md` caution remains important but is resolved by this split: a pure `Catd Z := τ (Fam (Core_cat Z))` layer alone would lose directed base-arrow structure if it replaced all directed families. Therefore the primary directed layer must be `Fam K`; `Catd Z` is only the core/path layer derived from it.

Documentation consolidation is also in scope: before or alongside implementation, the stable v3 decisions should be summarized in a single consolidated report so older planning reports can be retired without losing useful context.

## Current Fam/Core Architecture

### Implementation conventions and required interfaces

Below, notation such as `E : Fam K` means `E : τ (Fam K)`. The `Fam K` head itself is a `Grpd` code, following the existing `Functor A B : Grpd := Obj (Functor_cat A B)` convention.

The current section should remain readable without the historical/superseded material below. The implementation therefore depends on the following explicit interfaces:

```text
Fam_cat (K : Cat) : Cat
Fam (K : Cat) : Grpd

Transf_cat [A B] (F G : τ (Functor A B)) : Cat

tapp0_fapp0 [A B] [F G : τ (Functor A B)]
  (k : τ (Obj A)) (eta : τ (Obj (Transf_cat F G)))
  : τ (Hom B (fapp0 F k) (fapp0 G k))

tapp1_fapp0 [A B] [F G : τ (Functor A B)]
  [x y : τ (Obj A)] (eta : τ (Obj (Transf_cat F G))) (f : τ (Hom A x y))
  : τ (Hom B (fapp0 F x) (fapp0 G y))

Core_incl_func Z : τ (Functor (Core_cat Z) Z)

fapp0_func [A B] (u : τ (Obj A))
  : τ (Functor (Functor_cat A B) B)

fapp1_func [A B] (E : τ (Functor A B))
  [x y : τ (Obj A)]
  : τ (Functor (Hom_cat A x y) (Hom_cat B (fapp0 E x) (fapp0 E y)))

hom_con [A] (v : τ (Obj A)) [B] (F : τ (Functor B A))
  : τ (Functor (Op_cat B) Cat_cat)

fib_cov_tapp0_fapp0 [K] (E : τ (Fam K))
  [x y : τ (Obj K)] (f : τ (Hom K x y)) (u : τ (Obj (fapp0 E x)))
  : τ (Obj (fapp0 E y))
```

`tapp0_fapp0` is the diagonal component of an ordinary transfor. `tapp1_fapp0` is the arrow-indexed/naturality component. The Sigma-map object beta only needs `tapp0_fapp0`; the Sigma-map arrow beta needs `tapp1_fapp0` or an equivalent strict-naturality stable head.

For Cat-valued families, the codomain is `B = Cat_cat`, so these homs reduce through `Hom_cat Cat_cat A B ↪ Functor_cat A B`. Thus `tapp0_fapp0 k eta` and `tapp1_fapp0 eta f` can be used as ordinary functors between fibre categories.

Do not make a category of "functors over `K`" a prerequisite for this foundation. In the v3 kernel, `Transf_cat` is the internal language for maps of families and for sections. Any later bridge between `Transf_cat (Terminal_fam K) E` and functors `K -> Sigma_cat E` over `K` is derived infrastructure, not the definition of `Pi_cat`.

### Generic directed families

Use ordinary Cat-valued functors as the primary family/fibration interface:

```text
Fam_cat (K : Cat) : Cat
  := Functor_cat K Cat_cat

Fam (K : Cat) : Grpd
  := Obj (Fam_cat K)

Fibre_cat [K] (E : τ (Fam K)) (k : τ (Obj K)) : Cat
  ↪ fapp0 E k

Pullback_fam [A B] (E : τ (Fam B)) (F : τ (Functor A B)) : τ (Fam A)
  := comp_cat_fapp0 E F

Const_fam K A : τ (Fam K)
  := comp_cat_fapp0 (Obj_func A) (Terminal_func K)

Terminal_fam K : τ (Fam K)
  := Const_fam K Terminal_cat
```

This means the everyday substitution and fibre operations become ordinary functorial operations rather than special displayed-category operations.

`Fibre_cat E k` is only a stable readability/inference head for `fapp0 E k`. It should not carry additional displayed-category structure in the `Fam` layer. If this name keeps causing semantic confusion, rename the generic head to something neutral such as `Fam_app_cat E k`, and reserve `Fibre_cat` for compatibility aliases.

### Pi as sections

`Pi_cat` should be valid for any directed family `E : Fam K`, not only for a core-indexed family. Its foundation should be definitional/internal, not a later slice-category encoding:

```text
Pi_cat E := Transf_cat (Terminal_fam K) E
```

In this plan, "section" means exactly a natural transformation from the terminal family into `E`. It contains objects `s_k : E[k]` and coherent action along every base arrow `f : k -> k'`. This is why `Pi_cat E` is meaningful over general directed `K`.

There is a useful external reading of such an object as a functor `K -> Sigma_cat E` over `K`, but that should not be the source of truth. We do not yet need an internal category of "functors over `K`"; `Transf_cat (Terminal_fam K) E` is the available and intended expression of sections.

The primitive eliminator can remain:

```text
piapp0 : Obj (Pi_cat E) -> (k : Obj K) -> Obj (Fibre_cat E k)
```

but its intended source is component evaluation of the natural transformation `Terminal_fam K => E`.

### Sigma as real Grothendieck total

`Sigma_cat E` is the real Grothendieck/dependent-sum construction for any `E : Fam K`:

```text
Sigma_cat [K] (E : τ (Fam K)) : Cat
Sigma_proj1_func E : τ (Functor (Sigma_cat E) K)
```

Objects compute as:

```text
Obj (Sigma_cat E) ↪ Σ k : Obj K, Obj (Fibre_cat E k)
fapp0 (Sigma_proj1_func E) (Struct_sigma k u) ↪ k
```

For a transformation of directed families:

```text
eta : τ (Obj (Transf_cat E D))
```

add the induced functor between total categories:

```text
sigma_map_func eta : τ (Functor (Sigma_cat E) (Sigma_cat D))
```

with object computation:

```text
fapp0 (sigma_map_func eta) (Struct_sigma k u)
  ↪ Struct_sigma k (fapp0 (tapp0_fapp0 k eta) u)
```

and projection law:

```text
comp_cat_fapp0 (Sigma_proj1_func D) (sigma_map_func eta)
  ↪ Sigma_proj1_func E
```

The arrow action is also principled. A hom-object in `Sigma_cat E` can be read as:

```text
f     : τ (Hom K k k')
alpha : τ (Hom (Fibre_cat E k') (fib_cov_tapp0_fapp0 E f u) u')
```

Then `sigma_map_func eta` should map it to the same base arrow with the fibre arrow obtained by applying the component of `eta` at the target:

```text
fapp1_fapp0 (sigma_map_func eta) (Struct_sigma f alpha)
  ↪ Struct_sigma f (sigma_map_alpha eta f alpha)
```

where:

```text
sigma_map_alpha eta f alpha
  : τ (Hom
      (Fibre_cat D k')
      (fib_cov_tapp0_fapp0 D f (fapp0 (tapp0_fapp0 k eta) u))
      (fapp0 (tapp0_fapp0 k' eta) u'))
```

Conceptually:

```text
sigma_map_alpha eta f alpha
  = fapp1_fapp0 (tapp0_fapp0 k' eta) alpha
```

with its source typed by ordinary transfor naturality. Both source expressions should normalize through the arrow-indexed component:

```text
fib_cov_tapp0_fapp0 D f (fapp0 (tapp0_fapp0 k eta) u)
  ↔ fapp0 (tapp1_fapp0 eta f) u
  ↔ fapp0 (tapp0_fapp0 k' eta) (fib_cov_tapp0_fapp0 E f u)
```

If these strict-naturality folds are not yet available when `sigma_map_func` is implemented, keep `sigma_map_alpha` as a stable primitive head and add the computation rule only after `tapp1_fapp0` and its naturality rules typecheck. This is the corrected replacement for the old statement that a transformation becomes a displayed functor between `Fibration_cov_catd` objects.

### Core displayed categories

Core families are a specialization, not the main directed layer:

```text
Catd_cat (Z : Cat) : Cat
  := Fam_cat (Core_cat Z)

Catd (Z : Cat) : TYPE
  := τ (Fam (Core_cat Z))
```

Restore or preserve the core inclusion interface:

```text
Core_incl_func Z : τ (Functor (Core_cat Z) Z)
```

Then the compatibility spelling for a directed family restricted to paths/equivalences is:

```text
Fibration_cov_catd [Z] (M : τ (Fam Z)) : Catd Z
  := Pullback_fam M (Core_incl_func Z)
```

This keeps the semantic meaning of `Catd`: it is HoTT/core transport over equality/equivalence arrows, not arbitrary directed transport over every arrow of `Z`.

### Maps between core families

For `E D : Catd Z`, the primary map category should be:

```text
Functord_cat E D := Transf_cat E D
```

This supersedes the older plan:

```text
Functord_cat E D := Pi_cat (Functor_catd E D)
```

The `Pi(Functor_catd)` view can return later as an internal-hom/end-style bridge, but it should not be the foundation because it forces variance/coherence work before the basic `Fam` semantics is stable.

Old application/projection heads become derived convenience wrappers:

```text
Fibre_func FF k
  := tapp0_fapp0 k FF

fdapp0 FF k u
  := fapp0 (tapp0_fapp0 k FF) u

Transfd_cat FF GG
  := Hom_cat (Transf_cat E D) FF GG
```

So `fdapp0`, `Fibre_func`, `Transf_catd`, and `Transfd_cat` are not blockers for the `Fam/Core` migration. They may be reintroduced later only when a stable head is useful for rewriting or readability.

### Mixed variance and old `Functor_catd`

For arbitrary directed `K`, the pointwise assignment:

```text
k |-> Functor_cat (E k) (D k)
```

is not covariantly functorial when both `E,D : Fam K`: along `f : k -> k'`, `D(f)` gives postcomposition, but the domain side needs precomposition in the opposite direction.

The general constructor should therefore be mixed variance:

```text
Functor_fam [K]
  (E : τ (Fam (Op_cat K)))
  (D : τ (Fam K))
  : τ (Fam K)

Fibre_cat (Functor_fam E D) k
  ↪ Functor_cat (Fibre_cat E k) (Fibre_cat D k)
```

For core bases, `Op_cat (Core_cat Z)` reduces to `Core_cat Z`, so the old pointwise constructor can be recovered:

```text
Functor_catd [Z] (E D : Catd Z) : Catd Z
  := Functor_fam E D
```

where the source `E` is used contravariantly through path reversal/core duality.

### Contravariant displayed-family classifier

The `tmp-2007.md` note about `Catd_catd` is correct: for a general directed family `E : Fam K`, the assignment

```text
k |-> Catd_cat (Fibre_cat E k)
```

is naturally contravariant in `k`, not covariant. A base arrow:

```text
E(f) : Fibre_cat E k -> Fibre_cat E k'
```

induces pullback of core families:

```text
Catd_cat (Fibre_cat E k') -> Catd_cat (Fibre_cat E k)
```

So promote the existing v2 idea:

```text
Catd_func : τ (Functor (Op_cat Cat_cat) Cat_cat)
fapp0 Catd_func A ↪ Catd_cat A
```

and define:

```text
Catd_fam [K] (E : τ (Fam K)) : τ (Fam (Op_cat K))
  := comp_cat_fapp0 Catd_func (Op_func E)

Catd_catd [Z] (E : Catd Z) : Catd Z
  := core-specialization of Catd_fam E
```

This is the principled replacement for treating `Catd_catd` as a bare fibrewise rule.

## Replacement Sigma-Hom Direction

The generic directed Sigma hom should be formulated for:

```text
E : τ (Fam K)
x y : τ (Obj K)
u : τ (Obj (Fibre_cat E x))
v : τ (Obj (Fibre_cat E y))
```

not for arbitrary `E : Catd Z`. Its expected Grothendieck normal form is:

```text
Hom_cat (Sigma_cat E) (Struct_sigma x u) (Struct_sigma y v)
  ↪ Op_cat (Sigma_cat (sigma_hom_fam E x u y v))
```

Here `sigma_hom_fam` is not a new primitive constructor. It is a derived stable normal form for the composite:

```text
f : Hom_K(x,y)
  |-> E(f)(u) : E[y]
  |-> Hom_{E[y]}(E(f)(u), v) : Cat
```

First define the action of a family on a fixed fibre object:

```text
fam_tapp0_func [K] (E : τ (Fam K))
  [x y : τ (Obj K)] (u : τ (Obj (fapp0 E x)))
  : τ (Functor (Hom_cat K x y) (fapp0 E y))

fam_tapp0_func E x y u
  := comp_cat_fapp0
       (fapp0_func u)
       (fapp1_func E [x] [y])
```

with object computation folded to a stable head if useful:

```text
fapp0 (fam_tapp0_func E x y u) f
  ↪ fib_cov_tapp0_fapp0 E f u

fib_cov_tapp0_fapp0 E f u
  : τ (Obj (fapp0 E y))
```

Then define the fixed-endpoint hom functor by the existing contravariant hom helper:

```text
sigma_hom_fam [K] (E : τ (Fam K))
  (x : τ (Obj K)) (u : τ (Obj (fapp0 E x)))
  (y : τ (Obj K)) (v : τ (Obj (fapp0 E y)))
  : τ (Functor (Op_cat (Hom_cat K x y)) Cat_cat)

sigma_hom_fam E x u y v
  := hom_con v (fam_tapp0_func E x y u)
```

and its object computation is:

```text
fapp0 (sigma_hom_fam E x u y v) f
  ↪ Hom_cat
      (fapp0 E y)
      (fib_cov_tapp0_fapp0 E f u)
      v
```

where `f : Obj (Op_cat (Hom_cat K x y))`, i.e. semantically an arrow `x -> y` in `K`.

This is the directed formula that v2 was using under `Fibration_cov_catd`. In v3 it belongs directly to `Fam K` and `Sigma_cat E`; it should not be routed through core restriction.

For the core case `E : Catd Z = τ (Fam (Core_cat Z))`, the same Sigma-hom formula quantifies over core/path arrows. That gives the HoTT Sigma identity/equality story, not the full directed hom story of `Z`.

## Transport Packaging Status

The older report below proposes:

```text
transportd_sec [Z] (E : Catd Z) ...
```

as directed transport over arbitrary base arrows. That is no longer valid under `Catd Z := τ (Fam (Core_cat Z))`.

For the directed `Fam` layer, a global transport section is optional packaging, not the primary Sigma-hom construction. The primary construction is:

```text
fam_tapp0_func E x y u
sigma_hom_fam E x u y v := hom_con v (fam_tapp0_func E x y u)
```

If section-level packaging is later useful, it can be added as a derived stable head:

```text
transport_fam_sec [K] (E : τ (Fam K))
  (x : τ (Obj K)) (u : τ (Obj (Fibre_cat E x)))
  : τ (Obj
      (Pi_cat
        (Pullback_fam E
          (Sigma_proj1_func (Edge_fam K x)))))
```

where:

```text
Edge_fam K x : τ (Fam K)
Fibre_cat (Edge_fam K x) y ↪ Op_cat (Hom_cat K x y)
```

and:

```text
piapp0
  (transport_fam_sec E x u)
  (Struct_sigma y f)
↪ fib_cov_tapp0_fapp0 E f u
```

This should not block the first Sigma-hom implementation. If a core-only transport operation is needed, it should be a separate `transport_core_sec` or simply an instance of the family action where `K = Core_cat Z`.

## Replacement Implementation Sequence

1. Add `Fam_cat`, `Fam`, `Fibre_cat`/`Fam_app_cat`, `Const_fam`, `Terminal_fam`, and `Pullback_fam` as generic wrappers around existing functor-category infrastructure.
2. Restore/add `Core_incl_func Z`, define `Catd_cat Z := Fam_cat (Core_cat Z)` and `Catd Z := τ (Fam (Core_cat Z))`, then demote `Fibration_cov_catd M` to core restriction.
3. Add the ordinary transfor component interface from v2: `tapp0_fapp0`, `tapp1_fapp0`, identity/composition component rules, strict-naturality folds needed for arrow-indexed components, and the beta rule from any `tapp0_func`/`tapp1_*` packaging if that packaging is kept.
4. Define `Pi_cat E := Transf_cat (Terminal_fam K) E`, keep `piapp0` as component evaluation, and define `Functord_cat E D := Transf_cat E D` for core families.
5. Replace old `fdapp0`/`Fibre_func` usages with derived wrappers over `tapp0_fapp0` where a compatibility head is still helpful.
6. Generalize `Sigma_cat`, `Sigma_proj1_func`, and object/projection beta rules from `Catd` inputs to `Fam K` inputs.
7. Add `sigma_map_func eta` for `eta : τ (Obj (Transf_cat E D))`, with object beta and projection law. Add the arrow-action beta through `sigma_map_alpha` once `tapp1_fapp0` naturality folds are available; otherwise keep `sigma_map_alpha` as a stable head and postpone its computation rule.
8. Add `fam_tapp0_func`, the optional stable object-action fold `fib_cov_tapp0_fapp0 E f u`, and the derived `sigma_hom_fam := hom_con v (fam_tapp0_func E x y u)`.
9. Add the Sigma hom rule expressed through `sigma_hom_fam`.
10. Add `Functor_fam` with mixed variance, then recover old `Functor_catd` as the core-specialized alias.
11. Promote `Catd_func : τ (Functor (Op_cat Cat_cat) Cat_cat)`, define `Catd_fam E : τ (Fam (Op_cat K))`, and recover old `Catd_catd` as the core-specialized alias.
12. Add `Edge_fam K x` and `transport_fam_sec` only if a later section-level construction needs them.
13. Revisit `Transf_catd`, `Transfd_cat`, `homd_curry`, and `PredPi_catd` only after the generic `Fam`/`Sigma`/`Pi` layer typechecks.

## Replacement Test Plan

- Run after each implementation slice:
  - `lambdapi check -w emdash3.lp`
- Final validation:
  - `EMDASH_TYPECHECK_TIMEOUT=60s make check`

Required assertions for the revised foundation:

- `Fibre_cat (Const_fam K A) k ≡ A`.
- `Fibre_cat (Pullback_fam E F) a ≡ Fibre_cat E (fapp0 F a)`.
- `Fibre_cat (Fibration_cov_catd M) z ≡ fapp0 M z`.
- `Pi_cat E ≡ Transf_cat (Terminal_fam K) E`.
- `Functord_cat E D ≡ Transf_cat E D`.
- `Fibre_func FF k ≡ tapp0_fapp0 k FF` if the compatibility head is kept.
- `fdapp0 FF k u ≡ fapp0 (tapp0_fapp0 k FF) u` if the compatibility head is kept.
- `fapp0 (Sigma_proj1_func E) (Struct_sigma k u) ≡ k`.
- `fapp0 (sigma_map_func eta) (Struct_sigma k u) ≡ Struct_sigma k (fapp0 (tapp0_fapp0 k eta) u)`.
- `comp_cat_fapp0 (Sigma_proj1_func D) (sigma_map_func eta) ≡ Sigma_proj1_func E`.
- Once `tapp1_fapp0` naturality is ported: `fapp1_fapp0 (sigma_map_func eta) (Struct_sigma f alpha) ≡ Struct_sigma f (sigma_map_alpha eta f alpha)`.
- Once the source-normalization folds are stable: `sigma_map_alpha eta f alpha ≡ fapp1_fapp0 (tapp0_fapp0 k' eta) alpha`, with both source expressions normalized through `fapp0 (tapp1_fapp0 eta f) u`.
- `fapp0 (fam_tapp0_func E x y u) f ≡ fib_cov_tapp0_fapp0 E f u`.
- `sigma_hom_fam E x u y v ≡ hom_con v (fam_tapp0_func E x y u)`.
- `fapp0 (sigma_hom_fam E x u y v) f ≡ Hom_cat (fapp0 E y) (fib_cov_tapp0_fapp0 E f u) v`.
- `Hom_cat (Sigma_cat E) (Struct_sigma x u) (Struct_sigma y v) ≡ Op_cat (Sigma_cat (sigma_hom_fam E x u y v))`.
- Optional if section packaging is added: `Fibre_cat (Edge_fam K x) y ≡ Op_cat (Hom_cat K x y)`.
- Optional if section packaging is added: `piapp0 (transport_fam_sec E x u) (Struct_sigma y f) ≡ fib_cov_tapp0_fapp0 E f u`.
- `Fibre_cat (Functor_fam E D) k ≡ Functor_cat (Fibre_cat E k) (Fibre_cat D k)`.
- `Fibre_cat (Functor_catd E D) z ≡ Functor_cat (Fibre_cat E z) (Fibre_cat D z)` for core families.
- `fapp0 Catd_func A ≡ Catd_cat A`.
- `Fibre_cat (Catd_catd E) z ≡ Catd_cat (Fibre_cat E z)` for core families.

## Replacement Assumptions

- `emdash3.lp` may break compatibility with temporary v3 names.
- `emdash2.lp` remains read-only reference material.
- `Fam K = Obj (Functor_cat K Cat_cat)` is the primary directed family layer, with inhabitants `E : τ (Fam K)`.
- `Catd Z = τ (Fam (Core_cat Z))` is the HoTT/core displayed-family layer.
- `Sigma_cat E` is the real Grothendieck/dependent-sum total for `E : Fam K`.
- `Fibration_cov_catd M` is compatibility notation for core restriction, not totalization.
- `Pi_cat E` is definitionally the section category `Transf_cat (Terminal_fam K) E`. Do not require an internal category of functors over `K` to define sections.
- `Functord_cat E D` for core families is `Transf_cat E D`.
- `tapp0_fapp0` is the required diagonal component projection for ordinary transfors; `piapp0`, `fdapp0`, `Fibre_func`, and the object-action of `sigma_map_func` should be expressed through it.
- `tapp1_fapp0` or an equivalent arrow-indexed naturality head is required for the full arrow-action computation of `sigma_map_func`. Until those folds are stable, use `sigma_map_alpha` as the stable head for the fibre arrow of `sigma_map_func`.
- Old `Functor_catd`, `Catd_catd`, `Transf_catd`, and `Transfd_cat` should be reintroduced as derived/core-specialized bridges only after the generic `Fam` layer is stable.
- Do not introduce a primitive `SigmaHom_catd` for the foundational meaning. Use the derived composite `sigma_hom_fam E x u y v := hom_con v (fam_tapp0_func E x y u)`.
- `transport_fam_sec` is optional section-level packaging, not a prerequisite for the Sigma-hom rule.
- Higher cells remain ordinary homs in already-formed categories and are made iterable by operation-level repackaging heads, not by an infinite family of new cell constructors.

## Status of Earlier Sections

The sections below are retained as historical notes and as a checklist of stable-head ideas that may still be useful. They are not the current implementation plan where they conflict with the `Fam/Core` replacement above. In particular, these older claims are superseded:

- `Pi_cat` as primitive rather than `Transf_cat (Terminal_fam K) E`.
- `Functord_cat E D := Pi_cat (Functor_catd E D)` as the foundation.
- generic directed `transportd_sec E x u` for arbitrary `E : Catd Z`.
- treating `Fibration_cov_catd M` as the Grothendieck construction rather than core restriction.

## Historical Core Architecture Notes

- Promote `PiHom_catd` to `Hom_catd`.
  - Current `PiHom_catd E s t` is already essentially the desired operation.
  - Rename it or add a compatibility alias only temporarily.
  - Fibre rule:
    ```text
    Fibre_cat (Hom_catd E s t) z
      ↪ Hom_cat (Fibre_cat E z) (piapp0 s z) (piapp0 t z)
    ```
  - Pi hom rule:
    ```text
    Hom_cat (Pi_cat E) s t ↪ Pi_cat (Hom_catd E s t)
    ```

- Keep `Functor_catd` primitive.
  - `Functor_catd E D` remains the fibrewise displayed functor-category constructor.
  - `Functord_cat E D` remains a definition:
    ```text
    Functord_cat E D := Pi_cat (Functor_catd E D)
    ```
  - Therefore the hom of displayed functors is obtained from the generic Pi hom rule and the `Hom_catd (Functor_catd ...)` specialization.

- Keep `Transf_catd` as a stable primitive head.
  - Add or preserve:
    ```text
    Transf_catd [Z] [E D : Catd Z] (FF GG : Functord E D) : Catd Z
    ```
  - Its fibre rule should use extracted fibre functors:
    ```text
    Fibre_cat (Transf_catd FF GG) z
      ↪ Transf_cat (Fibre_func FF z) (Fibre_func GG z)
    ```
  - Add canonical normalization:
    ```text
    Hom_catd (Functor_catd E D) FF GG ↪ Transf_catd FF GG
    ```

- Define `Transfd_cat` by Pi, not as an independent level.
  - Use:
    ```text
    Transfd_cat FF GG := Pi_cat (Transf_catd FF GG)
    ```
  - Then:
    ```text
    Hom_cat (Functord_cat E D) FF GG
      ↪ Transfd_cat FF GG
    ```
    should either follow by unfolding plus the generic rules, or be added as a shortcut that joins the same normal form.

## Historical Sigma/Pi/Weakening Adjunction Notes

The current plan needs a sharper distinction between:

```text
Sigma_cat E : Cat
```

and the relative logical operation:

```text
Sigma_π : Catd (Sigma_cat E) -> Catd Z
```

where `π = Sigma_proj1_func E : Functor (Sigma_cat E) Z`.

`Sigma_cat E` is the context extension / total category for one displayed category `E : Catd Z`. It is not itself the whole left adjoint in the relative adjunction

```text
Sigma_π  ⊣  π*  ⊣  Pi_π.
```

In the current v3 kernel, the middle functor `π*` is already represented by pullback:

```text
Pullback_catd D (Sigma_proj1_func E)
```

for `D : Catd Z`. The relative `Sigma_π` and `Pi_π` constructors can be added later as displayed-category-level operations over `Z`. Their fibre rules should be expressed by restricting a family over `Sigma_cat E` to the fibre inclusion over each base object:

```text
fibre_intro_func E z : Functor (Fibre_cat E z) (Sigma_cat E)
fapp0 (fibre_intro_func E z) u ↪ Struct_sigma z u

Fibre_cat (Sigma_proj_catd E D) z
  ↪ Sigma_cat (Pullback_catd D (fibre_intro_func E z))

Fibre_cat (Pi_proj_catd E D) z
  ↪ Pi_cat (Pullback_catd D (fibre_intro_func E z))
```

These relative constructors are not required before the Sigma-hom slice, but the plan should avoid describing `Sigma_cat` alone as the adjoint `Sigma_π`.

The fragments needed immediately are the terminal/base-global adjunction fragments:

```text
Sigma_!  ⊣  !*  ⊣  Pi_!
```

where `!* A` is `Const_catd Z A`, `Sigma_! E` is `Sigma_cat E`, and `Pi_! E` is `Pi_cat E`.

Add or at least document the following generic stable heads before adding edge-specific helpers:

```text
sigma_intro_functord E
  : Functord E (Const_catd Z (Sigma_cat E))

fdapp0 (sigma_intro_functord E) z u
  ↪ Struct_sigma z u
```

This is the unit of `Sigma_! ⊣ !*`, i.e. Sigma introduction in context. It also packages all fibre inclusions internally. The fixed-endpoint edge map should be only a derived component:

```text
edge_at_func x y
  := piapp0 (sigma_intro_functord (Edge_catd Z x)) y

edge_at_func x y
  : Functor (Fibre_cat (Edge_catd Z x) y)
            (Sigma_cat (Edge_catd Z x))
```

and the existing fibre rule for `Edge_catd` then gives the desired source:

```text
Fibre_cat (Edge_catd Z x) y ↪ Op_cat (Hom_cat Z x y).
```

For `Pi_cat`, keep `piapp0` as the primitive eliminator/evaluation head, but identify it as the counit of `!* ⊣ Pi_!` by adding a displayed functor packaging:

```text
pi_eval_functord E
  : Functord (Const_catd Z (Pi_cat E)) E

fdapp0 (pi_eval_functord E) z s
  ↪ piapp0 s z
```

The dual unit is the constant-section operation:

```text
const_section_func Z A
  : Functor A (Pi_cat (Const_catd Z A))

piapp0 (fapp0 (const_section_func Z A) a) z
  ↪ a
```

This is the general source of any fixed-family constant section. Therefore `edge_const_sec` should not be foundational. It should either be a temporary alias or be replaced by a generic compatibility bridge saying that pulling `π*E` back along Sigma introduction is constant:

```text
Pullback_catd
  (Pullback_catd E (Sigma_proj1_func H))
  (piapp0 (sigma_intro_functord H) z)

  behaves as

Const_catd (Fibre_cat H z) (Fibre_cat E z).
```

More precisely, this should follow from three generic computation principles:

```text
Pullback_catd (Pullback_catd E F) G
  ↪ Pullback_catd E (comp_cat_fapp0 F G)

comp_cat_fapp0
  (Sigma_proj1_func H)
  (piapp0 (sigma_intro_functord H) z)
  ↪ const_func (Fibre_cat H z) Z z

Pullback_catd E (const_func A Z z)
  ↪ Const_catd A (Fibre_cat E z)
```

where `const_func A Z z : Functor A Z` is the ordinary constant functor at `z`. It can be implemented as a stable head or as the composite `Obj_func z ∘ Terminal_func A`, but a stable head may make the pullback rule easier to match.

If a direct rewrite from the pullback expression to `Const_catd` is too aggressive for Lambdapi, keep a generic stable head for this compatibility case, but make it generic in `H`, `E`, and `z`; do not introduce an edge-only primitive.

Similarly, section restriction should be a functoriality/substitution operation for `Pi_cat`, not an edge-specific construction:

```text
section_pullback_func F E
  : Functor (Pi_cat E) (Pi_cat (Pullback_catd E F))

piapp0 (fapp0 (section_pullback_func F E) s) a
  ↪ piapp0 s (fapp0 F a)
```

The fixed-endpoint transport section used in Sigma hom is then:

```text
transport_xy
  := fapp0
       (section_pullback_func (edge_at_func x y)
                              (Pullback_catd E (Sigma_proj1_func (Edge_catd Z x))))
       (transportd_sec E x u)
```

This keeps the Sigma-hom construction internal: `edge_at_func`, constant sections, and section restriction all come from generic Sigma/Pi/weakening primitives.

## Historical Omega-Iteration Principle

Do not introduce a fresh Lambdapi category constructor for each higher cell level, such as `Modf_catd`, `Modfd_cat`, `4Cell_catd`, etc.

Higher cells are ordinary homs in already-formed categories:

```text
modifications between eps eps' : Transfd_cat FF GG
  are Hom_cat (Transfd_cat FF GG) eps eps'
```

When these higher homs must be used functorially, they should be repackaged by operation-level heads into `Transfd_cat`-shaped data, following the emdash2 pattern:

```text
Hom_cat (Transfd_cat FF GG) eps eps'
  --operation-level repackaging-->
Transfd_cat (component_functor eps) (component_functor eps')
```

This is the role of later `tapp1_fapp1_func` / `tdapp1_fapp1_func`-style operations. They are stable heads for functorial operations, not new primitive cell levels. This preserves omega iteration without requiring an infinite sequence of Lambdapi symbols.

## Historical Documentation Consolidation Notes

- Add `reports/REPORT_EMDASH_V3_CONSOLIDATED.md`.
  - Summarize `PRD_EMDASH_V3_INITIAL_IDEA.md`, the emdash2 lessons that still matter, the accepted v3 architecture in this plan, and the next implementation sequence.
  - Include a superseded-reports index for existing `reports/*` files, distinguishing still-relevant references from outdated drafts.
  - Do not read, summarize, or reference `.scratchpad/`.
  - Historical note: at the time, this file was treated as the source of truth until the consolidated report existed. The current source of truth is now the `Fam/Core` replacement section above.

## Historical Internal Functoriality Work Still in Scope

- Internalize pullback in the displayed-category argument.
  - Add `Pullback_catd_func F : Functor (Catd_cat B) (Catd_cat A)`.
  - Object action:
    ```text
    fapp0 (Pullback_catd_func F) E ↪ Pullback_catd E F
    ```
  - Hom action should fold to `Pullback_funcd F`.

- Internalize ordinary composition more fully.
  - Add a functorial composition package in the functor being postcomposed:
    ```text
    comp_cat_func [X Y Z]
      : Functor
          (Functor_cat Y Z)
          (Functor_cat (Functor_cat X Y) (Functor_cat X Z))
    ```
  - Keep `comp_cat_cov_func G` as the object-action / stable postcomposition head.
  - Object action should compute as:
    ```text
    fapp0 (fapp0 comp_cat_func G) F ↪ comp_cat_fapp0 G F
    ```
  - Once this is stable, update `op_val_func` and similar internal pipelines to use the general functorial composition package rather than ad hoc postcomposition-only plumbing.

- Internalize `Catdd` constructors when needed.
  - Current `Catdd`, `Pullback_catdd`, `Functor_catdd`, and `Pi_catdd` remain useful.
  - Add functor-object versions for constructors whose morphism action matters:
    ```text
    Pullback_catdd_func F
    Functor_catdd_func B
    ```
  - Keep current `Pullback_catdd` and `Functor_catdd` as object-action aliases / stable object-level heads.
  - `Const_catdd [I Z] E` means weakening both `Z` and `E` into the extra `I` context.

- Make `Totald_catd` functorial in the displayed category variable.
  - The current fibre-only form is useful but semantically incomplete.
  - Keep `Total_intro_func` as the stable head for the induced functor on total categories:
    ```text
    Total_intro_func xy FF : Functor (Total_cat E) (Total_cat D)
    ```
    where `FF : Functord E (Pullback_catd D xy)`.
  - Keep `Total_intro_func_func xy` as the functor-object packaging in the displayed-functor argument:
    ```text
    fapp0 (Total_intro_func_func xy) FF ↪ Total_intro_func xy FF
    ```
  - A later `Totald_func Z : Functor (Catd_cat Z) Cat_cat` should have object action `H ↦ Sigma_cat H`.
  - Its hom action should be induced by the existing total-introduction package:
    ```text
    fapp1_func (Totald_func Z) H K
      ↪ Total_intro_func_func (id_func Z)
    ```
  - This should be paired with the identity-pullback normalization:
    ```text
    Pullback_catd K (id_func Z) ↪ K
    ```
    so the domain of `Total_intro_func_func (id_func Z)` is definitionally `Functord_cat H K`.
  - Once `Totald_func Z` exists, prefer defining or normalizing:
    ```text
    Totald_catd Z ↦ Fibration_cov_catd (Totald_func Z)
    ```
    rather than keeping `Totald_catd Z` as only a bare fibre rule.
  - Keep `Total_proj1_functord Z : Functord (Totald_catd Z) (ConstZ_catd Z)`.
    Its fibre functor should continue to compute to the ordinary projection:
    ```text
    Fibre_func (Total_proj1_functord Z) H ↪ Total_proj1_func H
    ```
    This remains important for `PredPi_catd` and for later generalized `Sigma`/weakening-pullback adjunction machinery.

## Historical Older Draft Material Intentionally Not Restored

The older saved draft contains two major decisions that should remain superseded:

- Do not restore the Functord-first foundation.
  - `Functord_cat` should not become primitive again merely to make `Pi_cat` a terminal displayed-functor instance.
  - Historical decision superseded by the `Fam/Core` replacement:
    ```text
    Pi_cat primitive
    Functor_catd primitive
    Functord_cat E D := Pi_cat (Functor_catd E D)
    ```
  - `piapp0` can still later be related to general displayed-functor evaluation, but this should not force the foundation back to the older primitive `Functord_cat` plan.

- Do not restore primitive `SigmaHom_catd`.
  - The older draft used:
    ```text
    SigmaHom_catd E x u y v : Catd (Op_cat (Hom_cat Z x y))
    ```
  - Historical decision, now superseded: Sigma hom was to be expressed by `transportd_sec`, restriction along the edge context, constant sections, and `Hom_catd`.
  - A named endpoint head is allowed later only as a derived normal form for that expression.

## Superseded Directed Displayed Transport

The transport primitive should be global over the edge context. Do not introduce a parallel `HomFrom_catd`; reuse the existing edge family:

```text
Edge_catd Z x : Catd Z
Fibre_cat (Edge_catd Z x) y ≡ Op_cat (Hom_cat Z x y)
```

Introduce a directed displayed transport/induction section:

```text
transportd_sec [Z] (E : Catd Z)
  (x : Obj Z) (u : E[x])
  : Obj
      (Pi_cat
        (Pullback_catd E
          (Total_proj1_func (Edge_catd Z x))))
```

Read this as:

```text
transportd_sec E x u [y, f : x -> y] : E[y]
```

For the Grothendieck case, add the beta rule:

```text
piapp0
  (transportd_sec (Fibration_cov_catd M) x u)
  (Struct_sigma y f)
↪ fib_cov_tapp0_fapp0 M f u
```

This is the directed analogue of HoTT transport/J for displayed categories. It is primitive for general `E : Catd Z`, with computation rules only for structured constructors such as `Fibration_cov_catd M`. It should not be derived from `homd_curry`; rather, `homd_curry` is later higher/off-diagonal packaging related to transport plus fibrewise hom.

For fixed endpoint `y`, the old fixed-target section is only a restriction of this global section. The endpoint inclusion should be obtained from generic Sigma introduction:

```text
edge_at_func x y :
  Functor (Op_cat (Hom_cat Z x y))
          (Sigma_cat (Edge_catd Z x))

edge_at_func x y
  := piapp0 (sigma_intro_functord (Edge_catd Z x)) y

edge_at_func x y f = Struct_sigma y f
```

If `edge_at_func` remains as a named symbol during implementation, it should be a compatibility alias for this component, not a new primitive concept.

The section-level helper needed to use this restriction is the generic pullback/substitution operation for sections:

```text
section_pullback_func F E
  : Functor (Pi_cat E) (Pi_cat (Pullback_catd E F))
```

where `s : Obj (Pi_cat E)` and `F : Functor A B`, with beta behavior:

```text
piapp0 (fapp0 (section_pullback_func F E) s) a
  ↪ piapp0 s (fapp0 F a)
```

The fixed-target section over the restricted family should come from the generic `const_section_func` plus the Sigma-introduction/pullback compatibility rule:

```text
edge_const_sec E x y v
  : Obj
      (Pi_cat
        (Pullback_catd
          (Pullback_catd E (Total_proj1_func (Edge_catd Z x)))
          (edge_at_func x y)))
```

with beta behavior:

```text
piapp0 (edge_const_sec E x y v) f ↪ v
```

As with `edge_at_func`, `edge_const_sec` may remain temporarily as a readable alias, but the source of truth should be the generic constant-section/unit operation. If the required pullback does not normalize all the way to `Const_catd`, introduce a generic compatibility head for this Sigma-introduction pullback case rather than an edge-only primitive.

## Superseded Sigma Hom Direction

The temporary endpoint heads `homd_eval_func` / `Homd_func` should not be treated as the v3 foundation. They may remain briefly as compatibility/debug heads, but the intended source of truth is:

```text
transportd_sec + section restriction + const_section + Hom_catd + Sigma_cat
```

For fixed endpoints `(x,u)` and `(y,v)`, define the restricted displayed family over the base-arrow category:

```text
Dxy :=
  Pullback_catd
    (Pullback_catd E (Total_proj1_func (Edge_catd Z x)))
    (edge_at_func x y)
```

Using pullback composition, projection-after-Sigma-introduction cancellation, and pullback-along-constant normalization, this family should reduce to:

```text
Dxy
  ↪ Const_catd
      (Fibre_cat (Edge_catd Z x) y)
      (Fibre_cat E y)

  ↪ Const_catd
      (Op_cat (Hom_cat Z x y))
      (Fibre_cat E y)
```

This does not make the transport section constant. It only says that all fibres of the indexed family are the same category `Fibre_cat E y`. The transport section can still vary with the arrow `f : x -> y`, which is exactly the intended Grothendieck behaviour.

Construct two sections over `Dxy`:

```text
transport_xy : Obj (Pi_cat Dxy)
const_v_xy   : Obj (Pi_cat Dxy)
```

where:

```text
transport_xy :=
  fapp0
    (section_pullback_func
      (edge_at_func x y)
      (Pullback_catd E (Total_proj1_func (Edge_catd Z x))))
    (transportd_sec E x u)

const_v_xy :=
  edge_const_sec E x y v
  -- eventually: generic constant section after Sigma-introduction pullback compatibility
```

After `Dxy` normalizes to the constant family, the second line should become simply:

```text
const_v_xy :=
  fapp0
    (const_section_func
      (Fibre_cat (Edge_catd Z x) y)
      (Fibre_cat E y))
    v
```

Then the Sigma hom classifier is the generic displayed hom:

```text
Hom_catd Dxy transport_xy const_v_xy
```

and the Sigma hom rule should be:

```text
Hom_cat (Sigma_cat E) (Struct_sigma x u) (Struct_sigma y v)
  ↪ Op_cat (Sigma_cat (Hom_catd Dxy transport_xy const_v_xy))
```

The current orientation convention is to keep the fixed-arrow base as `Op_cat (Hom_cat Z x y)`, matching the existing `Edge_catd` and `Homd_func` orientation. This can be revisited only if the full Sigma hom normal form is changed consistently.

For the Grothendieck probe case, the fibre of the displayed hom should compute to:

```text
Fibre_cat
  (Hom_catd Dxy transport_xy const_v_xy)
  f
↪ Hom_cat (M y) (fib_cov_tapp0_fapp0 M f u) v
```

No primitive `SigmaHom_catd` should be added for this meaning. If a stable endpoint head is useful later, it must be a derived normal form for this `Hom_catd` expression, not an independent primitive hom concept.

## Superseded Implementation Sequence

1. Consolidate documentation into `reports/REPORT_EMDASH_V3_CONSOLIDATED.md`, using this plan as the current source of truth and marking older reports as superseded where appropriate.
2. Promote `PiHom_catd` to `Hom_catd`, add the `Hom_catd (Functor_catd ...) ↪ Transf_catd ...` specialization, and verify `Transfd_cat` remains a Pi-defined level.
3. Add the generic Sigma/Pi/weakening adjunction fragments: `const_func`, `sigma_intro_functord`, `pi_eval_functord`, `const_section_func`, `section_pullback_func`, pullback-composition normalization, and only generic compatibility heads needed for pullback along Sigma introduction.
4. Add the internal functor-object versions of pullback, composition, `Catdd` constructors, and totalization, including the `Total_intro_func_func`-based hom action for `Totald_func`.
5. Add directed displayed transport over `Edge_catd`, derive `edge_at_func` from `sigma_intro_functord`, derive or alias the fixed constant section from the generic constant-section machinery, and add the Sigma hom rule expressed through `Hom_catd`.
6. Remove or demote `homd_eval_func` / `Homd_func` only after the new Sigma hom path has equivalent Grothendieck beta coverage.

## Superseded Test Plan

- Run after each implementation slice:
  - `lambdapi check -w emdash3.lp`
- Final validation:
  - `EMDASH_TYPECHECK_TIMEOUT=60s make check`

Required assertions for this foundation:

- `Fibre_cat (Hom_catd E s t) z ≡ Hom_cat (Fibre_cat E z) (piapp0 s z) (piapp0 t z)`.
- `Hom_cat (Pi_cat E) s t ≡ Pi_cat (Hom_catd E s t)`.
- `Hom_catd (Functor_catd E D) FF GG ≡ Transf_catd FF GG`.
- `Fibre_cat (Transf_catd FF GG) z ≡ Transf_cat (Fibre_func FF z) (Fibre_func GG z)`.
- `Transfd_cat FF GG ≡ Pi_cat (Transf_catd FF GG)`.
- `Hom_cat (Functord_cat E D) FF GG ≡ Transfd_cat FF GG`.
- `fdapp0 (sigma_intro_functord E) z u ≡ Struct_sigma z u`.
- `fdapp0 (pi_eval_functord E) z s ≡ piapp0 s z`.
- `piapp0 (fapp0 (const_section_func Z A) a) z ≡ a`.
- `piapp0 (fapp0 (section_pullback_func F E) s) a ≡ piapp0 s (fapp0 F a)`.
- `piapp0 (sigma_intro_functord (Edge_catd Z x)) y` has the fixed-endpoint `edge_at_func` type.
- `comp_cat_fapp0 (Sigma_proj1_func H) (piapp0 (sigma_intro_functord H) z) ≡ const_func (Fibre_cat H z) Z z`.
- `Pullback_catd E (const_func A Z z) ≡ Const_catd A (Fibre_cat E z)`.
- `fapp0 (Pullback_catd_func F) E ≡ Pullback_catd E F`.
- `fapp1_fapp0 (Pullback_catd_func F) FF ≡ Pullback_funcd F FF`.
- `fapp0 (fapp0 comp_cat_func G) F ≡ comp_cat_fapp0 G F`.
- `Fibre_cat (Totald_catd Z) H ≡ Sigma_cat H`.
- `fapp1_func (Totald_func Z) H K ≡ Total_intro_func_func (id_func Z)`.
- `Fibre_cat (Edge_catd Z x) y ≡ Op_cat (Hom_cat Z x y)`.
- `piapp0 (transportd_sec (Fibration_cov_catd M) x u) (Struct_sigma y f) ≡ fib_cov_tapp0_fapp0 M f u`.
- Restricting `transportd_sec E x u` along `edge_at_func x y` yields a section over the fixed-arrow family `Dxy`.
- The fixed-endpoint Sigma hom normalizes through `Hom_catd Dxy transport_xy const_v_xy`.
- In the Grothendieck case, the Sigma hom fibre computes to `Hom_cat (M y) (fib_cov_tapp0_fapp0 M f u) v`.
- No `Modf_catd` / `Modfd_cat` symbols are introduced.
- No primitive `SigmaHom_catd` is introduced for the foundational meaning.
- Existing `hom2_int`, `hom_`, `hom_con`, `Functor_catd`, `Catdd`, `PredPi_catd`, `Edge_catd`, and Groth transport sanity checks still pass.

## Superseded Assumptions

- `emdash3.lp` is allowed to break compatibility with temporary v3 names from earlier iterations.
- `emdash2.lp` remains read-only reference material.
- `Pi_cat` and `Functor_catd` remain primitive in v3.
- `Hom_catd` is the generic pointwise displayed hom; current `PiHom_catd` is its prototype.
- `Transf_catd` is a stable primitive head with a canonical rule from `Hom_catd (Functor_catd ...)`.
- The older proposal to make `Functord_cat` primitive again is superseded by the current decision: `Functord_cat E D := Pi_cat (Functor_catd E D)`.
- `Sigma_cat E` is context extension/totalization; the relative `Sigma_π` and `Pi_π` adjoints to pullback along `Sigma_proj1_func E` are separate displayed-category-level operations to add later if needed.
- `const_func`, `sigma_intro_functord`, `pi_eval_functord`, `const_section_func`, and `section_pullback_func` are the immediate computational fragments of the Sigma/Pi/weakening adjunctions.
- `transportd_sec` is a primitive directed displayed transport/induction operation for general `Catd`, with beta rules for `Fibration_cov_catd`.
- `Edge_catd` is the existing source of the edge context; do not introduce a duplicate `HomFrom_catd`.
- `edge_at_func` is provisional notation for the fixed-endpoint restriction map; it should be the `y`-component of `sigma_intro_functord (Edge_catd Z x)`, not a primitive.
- `edge_const_sec` is provisional notation for a constant section over the Sigma-introduction pullback; it should come from `const_section_func` plus generic compatibility, not an edge-only primitive.
- Sigma hom is expressed by `Hom_catd` after restricting transport and adding a constant section, not by a primitive `SigmaHom_catd`.
- Higher cells are represented by ordinary homs in existing categories and are made iterable by operation-level repackaging heads, not by an infinite family of new cell constructors.
- Old reports will not be moved by this implementation; a future consolidated report will make them safe for the user to retire afterward.
