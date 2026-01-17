# OUTLINE: More-internal `homd_cov` via `Total_proj1_func` (and curry/uncurry)

This document records the “more internal” redesign we converged on for the *dependent hom* construction
(`homd_cov`) in `emdash2.lp`, and how it feeds the corresponding “component-of-components” map
(the `*_fapp1_func` layer, analogous to `tapp1_fapp1_func` / `tdapp1_fapp1_func`).

Status: design only (no code changes in this outline).

---

## 0. Context: the problem with the current `homd_cov`

In `emdash2.lp` the current stable head is:

- `homd_cov` (draft):
  - inputs: `Z : Cat`, `E : Catd Z`, `W_Z : Obj Z`, `W_EW : Obj(Fibre_cat E W_Z)`, `D : Catd Z`,
    `FF : Obj(Functord_cat D E)`
  - output: a Cat-valued functor on a “2-simplex base” built using a `Product_catd` coupling.

The pain point is the explicit coupling (and “ad hoc feel”) of a fibre-object with a representable-ish
construction through `Product_catd`. It blocks a clean “internal” story where the base object is *not*
an external parameter but is obtained from a *single point* in a total category.

We want to:

- avoid `Product_catd` in the base shape,
- internalize the base object by using the projection `Total_proj1_func`,
- keep existing symbols as *stable heads* (for rewrite performance),
- and expose a more compositional “internal API” that reads like ordinary category theory.

---

## 1. Already-available building blocks in `emdash2.lp`

These already exist (or are definitional abbreviations):

- `op : Obj(Functor_cat Cat_cat Cat_cat)` with `fapp0 op A ↪ Op_cat A`.
- `comp_func_cat F G := comp_fapp0 Cat_cat F G` (definitional abbreviation).
- `hom_cov` and the internalized variant:
  - `hom_cov_func : (F : Obj(Functor_cat B A)) ↦ Obj(Functor_cat (Op_cat A) (Functor_cat B Cat_cat))`
    with β-rule `fapp0 (hom_cov_func F) X ↪ hom_cov A X B F`.
- `Total_proj1_func D : Obj(Functor_cat (Total_cat D) Z)` for `D : Catd Z`.
- `Op_func` turning `F : X⇒Y` into `Fᵒᵖ : Xᵒᵖ⇒Yᵒᵖ`.
- `Pullback_catd` and the key Grothendieck pullback rule:
  `Pullback_catd (Fibration_catd E) F ↪ Fibration_catd (E ∘ F)`.

We also note a convenience we can use without new primitives:

- pointwise opposite on Cat-valued functors (a.k.a. `op'`):
  - for `F : Obj(Functor_cat B Cat_cat)`, define `op' F := comp_func_cat op F`.
  - this is already “solved” by `comp_func_cat op`.

---

## 2. The missing classifier: uncurrying Cat-valued functors

The key technical gap is: Grothendieck totals (`Fibration_catd`) accept *Cat-valued functors*
of the form `R : Obj(Functor_cat A Cat_cat)`.

But the “internalized base object” route naturally produces a functor into a functor category:

- `K : Obj(Functor_cat A (Functor_cat B Cat_cat))`

We need to turn that into a single Cat-valued functor on a product base:

- `uncurry_cat K : Obj(Functor_cat (Product_cat A B) Cat_cat)`

Minimal (design) interface:

```text
uncurry_cat :
  Π [A B : Cat],
  Obj(Functor_cat A (Functor_cat B Cat_cat))
    → Obj(Functor_cat (Product_cat A B) Cat_cat)

β (objects):
  fapp0 (uncurry_cat K) (Struct_sigma a b)
    ↪ fapp0 (fapp0 K a) b
```

We do **not** need full `fapp1_func` computation for `uncurry_cat` immediately to state the new types;
we can keep `uncurry_cat` as a stable head with only the object β-rule (and add morphism rules later as needed).

Alternative engineering choice (same mathematics): instead of a general `uncurry_cat`, introduce a single
specialized stable-head for the specific `K` used by `homd_cov` (so `uncurry` never appears in user-facing types).

---

## 3. New “more internal” base (no `Product_catd`): reindex via `Total_proj1_func`

Fix `Z : Cat` and a displayed category `D : Catd Z`. Let

- `πD := Total_proj1_func D : Obj(Functor_cat (Total_cat D) Z)`.

We want a Cat-valued functor `R_D` on a base that includes:

- an object of `Total_cat D` (so it carries, semantically, a base object in `Z` plus a fibre object in `D`),
- and an additional “index” object (the “1-simplex” direction, typically an object of `Z`).

### 3.1 Build the “representable-in-context” layer without external `W_Z`

Use the already-internalized hom-covariant constructor at the identity:

- `H := hom_cov_func (@Id_func Z) : Obj(Functor_cat (Op_cat Z) (Functor_cat Z Cat_cat))`.

Precompose (on the `Op_cat Z` input) by `πD` (in opposite):

- `Op(πD) := Op_func (Total_cat D) Z πD : Obj(Functor_cat (Op_cat (Total_cat D)) (Op_cat Z))`.
- `K_D := comp_func_cat H Op(πD)
       : Obj(Functor_cat (Op_cat (Total_cat D)) (Functor_cat Z Cat_cat))`.

Intuition: an object `d̂ : Obj(Total_cat D)` determines `W_Z := πD(d̂) : Obj(Z)`, and then
`fapp0 K_D d̂` is (definitionally) the Cat-valued functor `hom_cov Z W_Z Z (Id_func Z)`.

### 3.2 Uncurry to a single Cat-valued functor on a product base

Uncurry:

- `R_D0 := uncurry_cat K_D
        : Obj(Functor_cat (Product_cat (Op_cat (Total_cat D)) Z) Cat_cat)`.

Optional: apply pointwise `op'` (i.e. postcompose by `op`) if we want to reverse (2-)cells in the Cat-values:

- `R_D := comp_func_cat op R_D0
       : Obj(Functor_cat (Product_cat (Op_cat (Total_cat D)) Z) Cat_cat)`.

Now we can form the Grothendieck total base category (the “2-simplex base”):

- `Base_D := Total_cat (Fibration_catd R_D) : Cat`.

This replaces the former `Total_cat(Product_catd ...)` shape while keeping the intended semantics:
the “base object” is internal (it comes from `d̂ : Total_cat D` via `πD`), and the simplex index
is the extra `z : Obj(Z)` in the product base.

---

## 4. New “more internal” `homd_cov` type

The new interface (call it `homd_cov_func3`) is:

```text
homd_cov_func3 :
  Π [Z : Cat] [E D : Catd Z] (FF : Obj(Functord_cat D E)),
  Obj(Functor_cat (Op_cat (Total_cat E))
       (Functor_cat Base_D Cat_cat))
```

Key properties:

- there is **no external** `W_Z : Obj(Z)` parameter;
  instead the object of `Total_cat E` plays the role of the “base point” (it carries `W_Z` via `Total_proj1_func E`).
- `FF : D⇒E` remains an input (even if it does not appear in the target type); this matches the existing style
  where some inputs are “semantic” and will only be used by the eventual computation rules.
- `Product_catd` is avoided in the base: the construction uses `Total_proj1_func D`, (opposite) precomposition,
  and Grothendieck totalization of a Cat-valued functor on a product base.

---

## 5. Consequence: the corresponding `*_fapp1_func` layer (analogy with `tapp1_fapp1_func`)

In `emdash2.lp`, the pattern for “component-of-components” is:

- a packaged functor (`tapp1_func_funcd` or `tdapp1_func_funcd`) whose:
  - object action (`fapp0`) is a “component functor” (`*_fapp0_*`), and
  - hom action (`fapp1_func`) is a “repackaging of modifications” (`*_fapp1_*`),
    e.g. `tapp1_fapp1_func` for ordinary modifications.

For the new `homd_cov_func3`-based formulation, the analogous design target is:

- a “more internal” displayed version (name suggestion):
  - `tdapp1_func_funcd3` whose codomain is built using `homd_cov_func3` instead of the old `homd_cov`,
    so that the “base point” is an object of `Total_cat E` (not a split `(X_Z,U_EX)` binder).

Then the corresponding hom-action is:

- `tdapp1_fapp1_func3`:
  - given a modification `α : Obj(Hom_cat (Transfd_cat FF GG) ϵ ϵ')`,
  - produce the displayed transfor between the induced “component functors” obtained by `fapp0` of `tdapp1_func_funcd3`.

Mechanically this follows the same pattern already used for `tapp1_fapp1_func`:

```text
rule fapp1_func (tdapp1_func_funcd3 ...) ϵ ϵ'  ↪  tdapp1_fapp1_func3 ... ϵ ϵ'
```

The main point of this outline is that the *type* of this `*_fapp1_func3` will now be expressed in terms of
`homd_cov_func3` (and therefore in terms of `Total_proj1_func` + uncurrying), rather than in terms of a
`Product_catd`-based “2-simplex base”.

---

## 6. Summary of what we gained

- `W_Z` is no longer an external parameter in the dependent-hom interface: it is internalized via
  total-category projection `Total_proj1_func`.
- The base category used to classify the “surface direction” is built without `Product_catd`, using:
  - `Total_proj1_func`,
  - (opposite) functor precomposition (`Op_func`),
  - curry/uncurry (via `uncurry_cat`),
  - Grothendieck totalization (`Fibration_catd` + `Total_cat`),
  - and optional pointwise opposite on Cat-values (`comp_func_cat op`).
- The `*_fapp1_func` layer (“action on modifications”) follows the existing `tapp1_*` / `tdapp1_*` pattern,
  but now targets the `homd_cov_func3`-based codomain, keeping the whole story more internal/compositional.

