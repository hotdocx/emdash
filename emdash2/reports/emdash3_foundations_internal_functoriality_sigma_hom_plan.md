# Plan Draft: v3 Foundations, Internal Functoriality, and Sigma Hom

## Summary

This draft supersedes the previous Functord-first wording. The corrected v3 foundation keeps `Pi_cat` primitive and keeps fibrewise constructors such as `Functor_catd` primitive. The missing general principle is the displayed pointwise hom, currently represented by `PiHom_catd`, which should be promoted/renamed to the generic `Hom_catd`.

For Sigma homs, the corrected source of truth is not a new primitive `SigmaHom_catd`. It is a directed displayed transport/induction section over the existing edge context `Edge_catd`, followed by the generic displayed hom `Hom_catd`.

The intended hierarchy is:

```text
Pi_cat        primitive
Functor_catd  primitive
Hom_catd      primitive/generic pointwise displayed hom

Functord_cat E D := Pi_cat (Functor_catd E D)

Transf_catd FF GG := stable canonical specialization of
  Hom_catd (Functor_catd E D) FF GG

Transfd_cat FF GG := Pi_cat (Transf_catd FF GG)
```

`Transf_catd` should remain a stable primitive head, not just a definitional alias. The canonical normalization should be a rule from the generic pointwise hom of a `Functor_catd` to this stable head:

```text
Hom_catd (Functor_catd E D) FF GG ↪ Transf_catd FF GG
```

## Core Architecture

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

## Omega-Iteration Principle

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

## Internal Functoriality Work Still in Scope

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

- Internalize `Catdd` constructors when needed.
  - Current `Catdd`, `Pullback_catdd`, `Functor_catdd`, and `Pi_catdd` remain useful.
  - Later functor-object versions should be added for constructors whose morphism action matters.
  - `Const_catdd [I Z] E` means weakening both `Z` and `E` into the extra `I` context.

- Make `Totald_catd` functorial in the displayed category variable.
  - The current fibre-only form is useful but semantically incomplete.
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

## Directed Displayed Transport

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

For fixed endpoint `y`, the old fixed-target section is only a restriction of this global section. Provisionally, that restriction can be expressed via:

```text
edge_at_func x y :
  Functor (Op_cat (Hom_cat Z x y))
          (Sigma_cat (Edge_catd Z x))

edge_at_func x y f = Struct_sigma y f
```

The exact construction of `edge_at_func` should later be replaced or generalized by the usual logic adjunction between `Sigma` and weakening/pullback; for now it is only a named description of the needed restriction map.

Two section-level helpers are needed to use this restriction:

```text
section_pullback F s
  : Obj (Pi_cat (Pullback_catd E F))
```

where `s : Obj (Pi_cat E)` and `F : Functor A B`, with beta behavior:

```text
piapp0 (section_pullback F s) a
  ↪ piapp0 s (fapp0 F a)
```

and a fixed-target section over the restricted family:

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

`edge_const_sec` may later be replaced by a more general weakening/constant-section operation once the `Sigma`/pullback adjunction machinery is introduced.

## Sigma Hom Direction

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

Construct two sections over `Dxy`:

```text
transport_xy : Obj (Pi_cat Dxy)
const_v_xy   : Obj (Pi_cat Dxy)
```

where:

```text
transport_xy := section_pullback (edge_at_func x y) (transportd_sec E x u)
const_v_xy   := edge_const_sec E x y v
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

## Test Plan

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
- `Fibre_cat (Edge_catd Z x) y ≡ Op_cat (Hom_cat Z x y)`.
- `piapp0 (transportd_sec (Fibration_cov_catd M) x u) (Struct_sigma y f) ≡ fib_cov_tapp0_fapp0 M f u`.
- Restricting `transportd_sec E x u` along `edge_at_func x y` yields a section over the fixed-arrow family `Dxy`.
- The fixed-endpoint Sigma hom normalizes through `Hom_catd Dxy transport_xy const_v_xy`.
- In the Grothendieck case, the Sigma hom fibre computes to `Hom_cat (M y) (fib_cov_tapp0_fapp0 M f u) v`.
- No `Modf_catd` / `Modfd_cat` symbols are introduced.
- No primitive `SigmaHom_catd` is introduced for the foundational meaning.
- Existing `hom2_int`, `hom_`, `hom_con`, `Functor_catd`, `Catdd`, `PredPi_catd`, `Edge_catd`, and Groth transport sanity checks still pass.

## Assumptions

- `emdash3.lp` is allowed to break compatibility with temporary v3 names from earlier iterations.
- `emdash2.lp` remains read-only reference material.
- `Pi_cat` and `Functor_catd` remain primitive in v3.
- `Hom_catd` is the generic pointwise displayed hom; current `PiHom_catd` is its prototype.
- `Transf_catd` is a stable primitive head with a canonical rule from `Hom_catd (Functor_catd ...)`.
- `transportd_sec` is a primitive directed displayed transport/induction operation for general `Catd`, with beta rules for `Fibration_cov_catd`.
- `Edge_catd` is the existing source of the edge context; do not introduce a duplicate `HomFrom_catd`.
- `edge_at_func` is provisional notation for the fixed-endpoint restriction map and will later be generalized via the `Sigma`/weakening-pullback adjunction.
- Sigma hom is expressed by `Hom_catd` after restricting transport and adding a constant section, not by a primitive `SigmaHom_catd`.
- Higher cells are represented by ordinary homs in existing categories and are made iterable by operation-level repackaging heads, not by an infinite family of new cell constructors.
- Old reports will not be moved by this implementation; a future consolidated report will make them safe for the user to retire afterward.
