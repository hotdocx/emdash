# SYNTAX_SURFACE.md

Surface type-theoretic syntax for **emdash2** (ω-categories, displayed categories, transfors).

This document describes the *intended surface language* and how it is meant to elaborate to the
kernel implemented in `emdash2.lp`.

Important discipline:

- Functoriality / naturality / contravariance are carried by **binder notation** and by *classifier*
  declarations (e.g. “`ϵ : Transf_cat(F,G)`”), not by explicit “naturality proof terms” in typing rules.
- Many kernel projections are **silent** at the surface level (like `τ` in Lambdapi).

Operational semantics (reductions) are implemented by Lambdapi rewrite rules and are documented
separately; this file focuses on surface *formation/typing*.

Status note (2026-02-09):

- `homd_` has computational Grothendieck/Grothendieck pointwise rules.
- `homd_curry` / `Homd_func` are active computational bridges for total-hom shapes.
- `homd_int` remains partially interface-level.
- strict naturality/exchange and adjunction triangle rules are present in draft phases.

Notation compatibility (`EMAIL.md` terminology):

- `:^f` corresponds to the functorial reading used here (default `x : A`).
- `:^n` corresponds to “natural-index discipline”; in this document that role is split between
  explicit context roles (`:^o`, `:^-`) and transfor-intro discipline.
- For arrow-indexed dependent contexts (e.g. terms using `f : z → z'`), we currently default to
  the `:^f` intent for base binders; `:^o` is explicit and specialized.

## 1. Binder modes (variance)

We use three binder annotations for variables ranging over objects of categories.

### 1.1 Functorial binder: `x : A`

`x : A ⊢ …`

Meaning: `x` is a *functorial index* (a variable meant to vary functorially). This is the default
when the dependency arises from a functor object (an object of a functor-category).

Example:

- `F : A → B` means “`x : A ⊢ F[x] : B`”.

### 1.2 Contravariant binder: `x :^- A`

`x :^- A ⊢ …`

Meaning: `x` is a *contravariant index*, used for “accumulation”/composition laws of arrow-indexed
components (e.g. `ϵ_(f)`).

This binder is preferred over writing `A^op` in surface syntax.

### 1.3 Object-only binder: `x :^o A`

`x :^o A ⊢ …`

Meaning: `x` is **object-only**: substitution is only along *paths* (equalities) in `Obj(A)`; we do
**not** assume any implicit transport along base arrows `f : x → y` in `A`.

This binder is used when we intentionally restrict to object-only reasoning. In current elaboration
milestones, arrow-indexed dependent contexts default to functorial intent (`:^f`) unless stated otherwise.

## 2. Silent elaborations (“τ-like” behavior)

The following are expected to be silent in surface syntax and inserted by elaboration:

- `τ` (decoding a `Grpd`-code to an actual type)
- `Fibre_cat` (fibre of a displayed category): we write `E[x]` and elaborate to `Fibre_cat E x`
- `fapp0` (object-action of a functor): we write `F[x]` and elaborate to `fapp0 F x`
- “diagonal components” of transfors:
  - `ϵ[x]` is the surface reading of `ϵ : Transf_cat(F,G)` (no explicit `tapp0_fapp0`)
  - `ϵ[e]` is the surface reading of `ϵ : Transfd_cat(FF,GG)` (no explicit `tdapp0_fapp0`)

Special silent coercion (Grothendieck):

- If the user has a functorial family `D0 : (z:Z ⊢ D0[z] : Cat)` (i.e. `D0 : Z ⟶ Cat`),
  then the displayed category `Fibration_cov_catd D0 : Catd Z` is *silently* available at the surface,
  and we keep the functorial binder `z:Z` for `D0[z]`.

For a generic displayed category `E : Catd Z` (not known to be Grothendieck), we use `z:^o Z`.

## 3. Core judgments (ω-categorical reading)

Judgments are written in a TT style using `⊢` lines.

Core formation:

```
⊢ C : Cat
⊢ x : C
⊢ y : C
⊢ Hom_C(x,y) : Cat
```

Arrow (1-cell) binder discipline:

```
⊢ C : Cat
x :^- C, y : C ⊢ f : x → y
```

Internally, `x : C` abbreviates `x : τ(Obj C)` and `f : x → y` abbreviates
`f : τ(Obj(Hom_cat C x y))`.

Identity and composition (surface):

```
⊢ C : Cat
⊢ x : C
⊢ id_x : x → x

⊢ C : Cat
⊢ x, y, z : C
g : y → z, f : x → y ⊢ g ∘ f : x → z
```

In the kernel, `comp_fapp0` is the pointwise constructor for `g∘f`, while `comp_func` is its internal
functorial packaging `∘ : Hom(y,z)×Hom(x,y) → Hom(x,z)`.

Higher cells iterate by taking hom-categories again:

- 2-cells between `f,g : x→y` are objects of `Hom_cat (Hom_cat C x y) f g`, etc.

## 4. Functors

Classifier reading:

```
⊢ A : Cat
⊢ B : Cat
⊢ F : A → B
x : A ⊢ F[x] : B
```

The action on arrows `F[f]` is **surface-silent**: writing `x:A` already conveys functoriality.

Optional explicit form (recommended for debugging and paper examples):

```
x :^- A, y : A, f : x → y ⊢ F1[f] : F[x] → F[y]
```

This elaborates to the same kernel stable head as the silent form (`fapp1_fapp0`-style arrow action).

## 5. Displayed categories and displayed functors

Displayed categories:

```
⊢ Z : Cat
⊢ E : Catd Z
z :^o Z ⊢ E[z] : Cat
```

Displayed functors (slice-style over the same base):

```
⊢ Z : Cat
⊢ E : Catd Z
⊢ D : Catd Z
⊢ FF : E ⟶_Z D
z :^o Z, e : E[z] ⊢ FF[e] : D[z]
```

Internally, this elaborates to:

- `E[z]` ↦ `Fibre_cat E z`
- `FF[e]` ↦ `fdapp0 FF z e`

## 6. Transfors (ordinary) and explicit arrow-indexed components

Classifier reading:

```
⊢ A : Cat
⊢ B : Cat
⊢ F : A → B
⊢ G : A → B
⊢ ϵ : Transf(F,G)
x : A ⊢ ϵ[x] : F[x] → G[x]
```

Explicit off-diagonal (arrow-indexed) component:

```
⊢ A : Cat
⊢ B : Cat
⊢ F : A → B
⊢ G : A → B
⊢ ϵ : Transf(F,G)
x :^- A, y : A, f : x → y ⊢ ϵ_(f) : F[x] → G[y]
```

This is the surface form of the internal stable head `tapp1_fapp0` (via `tapp1_*` packaging).

## 7. “Over a base arrow” displayed morphisms (`→_f`)

Let `Z : Cat`, `E : Catd Z`.

- Base arrow: `f : z → z'` in `Z`
- Displayed arrow over `f`: `σ : e →_f e'` where `e : E[z]` and `e' : E[z']`

This is the Grothendieck/simplicial “morphism over a base edge” notion used by the `homd_*`
layer.

## 8. Dependent-hom (simplicial) components: `homd_int`

Given:

- `Z : Cat`
- `E : Catd Z`
- `D0 : (z:Z ⊢ D0[z] : Cat)` (a functorial family, `Z ⟶ Cat`)
- `FF : (z:^o Z, d : D0[z] ⊢ FF[d] : E[z])` (a probe into `E`)

For `σ : homd_int(Z,E,D0,FF)`, we read:

```
z:^o Z, e:E[z], z':Z, f:z→z', d:D0[z'] ⊢ σ : e →_f FF[d]
```

Practical note:

- In current kernel computation, many total-hom normalizations proceed through `homd_curry` / `Homd_func`.
- Treat `homd_int` primarily as an internal interface/pipeline head unless a concrete computation rule is known.

## 9. Displayed transfors and explicit simplicial/off-diagonal components

Let:

- `E0 : (z:Z ⊢ E0[z] : Cat)` (i.e. `E0 : Z ⟶ Cat`)
- `FF, GG : (z:^o Z, e:E0[z] ⊢ FF[e] : D[z])` (displayed functors out of `∫E0`)
- `ϵ : Transfd_cat(FF,GG)`

Classifier reading (diagonal component; silent `tdapp0_*`):

```
z:^o Z, e:E0[z] ⊢ ϵ[e] : FF[e] → GG[e]
```

Explicit simplicial/off-diagonal component (analogue of ordinary `ϵ_(f)`):

```
z:^o Z, e:E0[z], z':Z, f:z→z', e':E0[z'], σ:e→_f e' ⊢ ϵ_(σ) : FF[e] →_f GG[e']
```

This is the surface reading of the internal `tdapp1_int_*` packaging (in particular `tdapp1_int_fapp0_transfd`)
that turns a displayed transfor into its over-a-base-arrow components.
