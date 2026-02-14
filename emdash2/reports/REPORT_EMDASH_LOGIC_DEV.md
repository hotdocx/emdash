# REPORT — emdash2 logical development (Option A)

Date: 2026-02-06  
Repo: `/home/user1/emdash2`  
Target: `emdash2.lp`

## Executive summary

This report proposes **Option A**:

> Add only `Functor_catd` and `Transf_catd` (and a companion projection `Fibre_transf`) to `emdash2.lp` **without** adding any definitional equality (rewrite) equating displayed functors/transfors with sections of these new displayed categories.

The goal is to unlock the **pointwise / “partial discharge”** surface syntax described in `EMAIL.md` while staying consistent with the current kernel architecture and avoiding premature rewrite/unification commitments that may compromise termination/confluence.

## Context: what exists today

`emdash2.lp` currently has:

- Displayed categories (isofibration-like families):
  - `Catd : Π (Z : Cat), TYPE`
  - `Fibre_cat : Π [Z : Cat] (E : Catd Z) (z : τ (Obj Z)), Cat`
  - `Terminal_catd : Π (Z : Cat), Catd Z`
  - Several constructors with **fibre computation** rules (e.g. Grothendieck `Fibration_cov_catd`, `Product_catd`, etc.).

- Displayed functors and displayed transfors as *categories* (slice-style, fixed base):
  - `Functord_cat : Π [Z : Cat], Catd Z → Catd Z → Cat`
  - `Transfd_cat : Π [Z : Cat] [E D : Catd Z], τ (Functord E D) → τ (Functord E D) → Cat`
  - Definitional identification: `Hom_cat (Functord_cat E D) FF GG ↪ Transfd_cat FF GG`.

- Pointwise projection of a displayed functor into a fibre functor:
  - `Fibre_func : Π … (FF : τ (Functord E D)) (z : τ (Obj Z)), τ (Functor (Fibre_cat E z) (Fibre_cat D z))`
  - plus an object-level β-rule: applying `Fibre_func FF z` reduces to `fdapp0` on objects.

Crucial constraints (architectural):

- `Functord_cat` and `Transfd_cat` are declared as **`constant symbol`** today. Therefore, we cannot currently add rewrite rules with head `Functord_cat` or `Transfd_cat`.
- More importantly, for general `Catd Z` the development intentionally does **not** yet provide a canonical computational account of transport/reindexing along arbitrary base arrows. Most `Catd` constructors currently compute only at the level of fibres.

## Motivation: the missing pointwise displayed type

The surface-syntax motivation in `EMAIL.md` is:

- For `FF : τ (Functord_(Z) E D)`, we already have the judgemental reading
  - `z :^f Z, e :^f E[z] ⊢ FF[e] : D[z]`.
- We want to be able to *partially discharge* the fibre variable:
  - `z :^f Z ⊢ FF_[z] : E[z] → D[z]`.

To make the type `E[z] → D[z]` expressible as an object of kind `Catd Z` (so it can appear under a `z :^f Z` binder), we need a displayed category whose fibre at `z` is the functor category between the fibres:

> `Functor_cat (Fibre_cat E z) (Fibre_cat D z)`.

Similarly for displayed transfors:

> a displayed category whose fibre at `z` is `Transf_cat (FF[z]) (GG[z])`.

Option A provides exactly these pointwise families, with computation only at the fibre level.

## Proposed additions (Option A)

### 1) `Functor_catd` (displayed functor-category, pointwise on fibres)

Add a new symbol:

```lambdapi
constant symbol Functor_catd : Π [Z : Cat], Π (E D : Catd Z), Catd Z;
```

with a fibre computation rule:

```lambdapi
rule Fibre_cat (Functor_catd $E $D) $z
  ↪ Functor_cat (Fibre_cat $E $z) (Fibre_cat $D $z);
```

Interpretation:

- `Functor_catd E D` is a displayed category over `Z`.
- Its fibre over `z : Obj Z` is the ordinary functor category between the fibre categories `E[z]` and `D[z]`.

This is intentionally *only* a pointwise/fibrewise computation. It does not assert anything about:

- morphisms of the total displayed category over non-identity base arrows,
- how these fibres vary functorially in `z`,
- or how sections of this family relate to displayed functors.

This matches the existing “fibrewise-only” philosophy for constructors like `Product_catd`:

- `Product_catd` computes on fibres by definition, while the full “over a base arrow” semantics is deferred until a cleavage/transport interface is stabilized.

### 2) `Transf_catd` (displayed category of transfors between fibre functors)

Add:

```lambdapi
constant symbol Transf_catd : Π [Z : Cat], Π [E D : Catd Z],
  Π (FF GG : τ (Functord E D)),
  Catd Z;
```

with a fibre computation rule:

```lambdapi
rule Fibre_cat (Transf_catd $FF $GG) $z
  ↪ Transf_cat (Fibre_func $FF $z) (Fibre_func $GG $z);
```

Interpretation:

- `Transf_catd FF GG` is a displayed category over `Z`.
- Its fibre over `z` is the ordinary transformation category between the projected fibre functors `FF[z]` and `GG[z]`.

Again: fibrewise-only computation.

### 3) `Fibre_transf` (project a displayed transfor to a fibre transfor)

To make `Transf_catd` usable in the intended “partial discharge” story, add a stable projection analogous to `Fibre_func`:

```lambdapi
symbol Fibre_transf : Π [Z : Cat], Π [E D : Catd Z],
  Π [FF GG : τ (Functord E D)],
  Π (ϵ : τ (Transfd FF GG)),
  Π (z : τ (Obj Z)),
  τ (Transf (Fibre_func FF z) (Fibre_func GG z));
```

and a β-rule stating that its pointwise components are the existing displayed components `tdapp0_fapp0`:

```lambdapi
rule @tapp0_fapp0
    (Fibre_cat $E $z)
    (Fibre_cat $D $z)
    (@Fibre_func $Z $E $D $FF $z)
    (@Fibre_func $Z $E $D $GG $z)
    $u
    (@Fibre_transf $Z $E $D $FF $GG $ϵ $z)
  ↪ @tdapp0_fapp0 $Z $E $D $FF $GG $z $u $ϵ;
```

Rationale:

- `tdapp0_fapp0` is the already-established stable head for the **diagonal component** of a displayed transfor at a base object `z` and a fibre object `u : E[z]`.
- `Fibre_transf` packages those components into an object of the ordinary `Transf_cat` between the fibre functors, which is precisely what `Transf_catd`’s fibres are made of.

## What Option A explicitly does NOT do (yet)

### No definitional equality “displayed functor = section”

Option A does **not** add a rewrite rule or unification rule equating:

- `Functord_cat E D`
  with
- `Functord_cat (Terminal_catd Z) (Functor_catd E D)` (sections of the pointwise functor family).

And similarly, it does not equate:

- `Transfd_cat FF GG`
  with
- `Functord_cat (Terminal_catd Z) (Transf_catd FF GG)` (sections of pointwise transfors).

Reason (semantic + engineering):

1. **Semantic gap (currently intentional):** In the current kernel, for general `Catd Z` we do not have a stabilized computational account of how objects transport along base 1-cells. Sections of `Functor_catd E D` would require exactly such transport to express “functoriality in `z`”.
2. **Rewrite discipline:** Both `Functord_cat` and `Transfd_cat` are declared `constant symbol`, and changing that is a nontrivial kernel decision. Even if changed, adding “sections = displayed functors” as definitional equality risks introducing rewrite loops or collapsing distinctions too early.

Option A therefore keeps these notions separate for now:

- `Functord_cat E D` is the *primitive* slice-style category of displayed functors (already used pervasively).
- `Functor_catd E D` is a *pointwise* displayed family enabling partial discharge and pointwise reasoning.

## Expected benefits

### 1) Enables the intended partial discharge typing

With `Functor_catd`, one can express, at least pointwise:

- `z ⊢ FF_[z] : Functor (E[z]) (D[z])`

where `FF_[z]` corresponds to `Fibre_func FF z` (already present).

With `Transf_catd` and `Fibre_transf`, one can express pointwise transfors:

- `z ⊢ ϵ_[z] : Transf (FF_[z]) (GG_[z])`

where `ϵ_[z]` corresponds to `Fibre_transf ϵ z`.

This directly supports the “discharge the fibre variable, then discharge the base variable” narrative, *without* committing to a global Π/section definitional equation.

### 2) Minimal risk to termination / confluence

Option A adds:

- two new constructors whose only computation is on `Fibre_cat`,
- and one projection (`Fibre_transf`) with a β-rule into an already-stable head (`tdapp0_fapp0`).

This pattern matches existing design motifs in `emdash2.lp`:

- keep conversion cheap by giving small stable heads,
- compute only in controlled directions (β-like rewrites),
- use unification rules for elaboration hints when needed, but avoid introducing definitional equalities that encode “η-like” principles globally.

### 3) Aligns with the “fibrewise-only for Catd” stage of the development

`Functor_catd` and `Transf_catd` are deliberately “fibrewise constructors”. They do not force the project to decide the full semantics of `Catd` morphisms over base arrows today.

## Follow-up work (not part of Option A)

Option A is a stepping stone. After it lands and typechecks, the next architectural decisions can be made with more evidence:

1. **A general “sections/Π” constructor for displayed categories** (if desired), likely as a separate stable head rather than by reusing `Functord_cat (Terminal_catd Z) _` immediately.
2. **A transport/cleavage interface for `Catd`** so we can compute (or at least reason uniformly) about morphisms over non-identity base arrows for more constructors.
3. **Relating displayed functors/transfors to sections** via explicit maps (curry/uncurry) and/or carefully oriented rewrite rules, once the above interfaces exist and rewrite risks are better understood.

## Recommendation

Implement Option A first:

- Add `Functor_catd` and its `Fibre_cat` computation rule.
- Add `Transf_catd` and its `Fibre_cat` computation rule.
- Add `Fibre_transf` and a β-rule linking it to `tdapp0_fapp0`.
- Add 1–2 `assert` sanity checks exercising these reductions (in the style already used throughout `emdash2.lp`).

This achieves the immediate expressive goal (pointwise types for partial discharge) while keeping the kernel conservative and computationally well-behaved.

