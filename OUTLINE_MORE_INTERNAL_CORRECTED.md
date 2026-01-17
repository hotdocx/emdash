# OUTLINE: More-internal formulation (corrected) — `hom_cov_func` / nested `Transf_cat` / `homd_cov5`

This note is a corrected handover plan for enhancing `emdash2.lp` toward a more “internal”
formulation of:

- the outer-indexed component packaging for transfors (`tapp1_*`), and
- the analogous displayed/dependent packaging (`tdapp1_*`) driven by the dependent-hom constructor (`homd_cov`).

It is self-contained relative to the current state of `emdash2.lp` (no code changes are performed here).

---

## 0) Current state (key facts in `emdash2.lp`)

### Ordinary hom-covariant functor

The file already contains:

- `hom_cov` (stable head):
  - `hom_cov A W B F : Obj(Functor_cat B Cat_cat)`
  - with computation `fapp0 (hom_cov A W B F) Y ↪ Hom_cat A W (fapp0 F Y)`.

- `hom_cov_func` (already internalizes `W`):
  - `hom_cov_func : Π [A] [B] (F : Obj(Functor_cat B A)), Obj(Functor_cat (Op_cat A) (Functor_cat B Cat_cat))`
  - with β-rule `fapp0 (hom_cov_func F) X ↪ hom_cov A X B F`.

So the “make `W` internal” step is already solved for `hom_cov`.

### Existing `tapp1_*` packaging (outer index is currently external)

Currently (simplified) the file has:

- `tapp1_func_funcd : Π X_A, Obj(Functor_cat (Transf_cat F G) (Functord_cat (Fibration_catd (hom_cov X Id)) (Fibration_catd (hom_cov (F X) G))))`

so `X_A` is a *binder* (external index) in the type.

### Existing projection mechanisms (important for non-circularity)

The file already uses *projection* operations to access components:

- ordinary components (inner/subscript level): `tapp0_func` / `tapp0_fapp0`
- displayed components: `tdapp0_func` / `tdapp0_fapp0`

These projections are intended to be “more primitive” than `tapp1_fapp1_func` / `tdapp1_fapp1_func`,
so that nested `Transf_cat` / `Transfd_cat` formulations are not circular: components are obtained by
`tapp0_*` / `tdapp0_*`, not by “re-using `tapp1`”.

---

## 1) Target improvement: internalize the *outer index* using nested `Transf_cat`

### 1.1 The type-correct internalization for `tapp1` (ordinary case)

Goal: avoid an explicit binder `X_A : Obj(A)` in `tapp1_func_funcd`.

Key observation: `hom_cov_func` already gives:

- for `Id_A : A⇒A`, a functor `H0 := hom_cov_func (Id_A) : A^op ⇒ (A ⇒ Cat)`.
- for `G : A⇒B`, a functor `hom_cov_func G : B^op ⇒ (A ⇒ Cat)`.

To get a functor of shape `A^op ⇒ (A ⇒ Cat)` from `hom_cov_func G`, precompose by `F^op`:

- `F^op : A^op ⇒ B^op` is `Op_func A B F`.
- define `H1 := (hom_cov_func G) ∘ F^op : A^op ⇒ (A ⇒ Cat)`.

Then the “more internal” `tapp1` target is:

```text
tapp1_func_funcd5 F G :
  Obj(Functor_cat (Transf_cat F G) (Transf_cat H0 H1)).
```

This is the correct replacement for earlier ill-typed attempts like
`Fibration_catd (hom_cov_func ...)` (those are ill-typed because `Fibration_catd` expects a functor
`A⇒Cat`, not `A^op⇒(A⇒Cat)`).

### 1.2 How components are accessed (non-circular operational semantics)

Given `ϵ : Obj(Transf_cat F G)`, the term

```text
fapp0 (tapp1_func_funcd5 F G) ϵ : Obj(Transf_cat H0 H1)
```

is an *outer* transformation whose index is `X : Obj(A)` (object of `A^op`).

Components are accessed by applying `tapp0_*` repeatedly:

1) Apply `tapp0_*` once to project the outer component at `X`
   (this yields a transformation between Cat-valued functors on `A`).

2) Apply `tapp0_*` a second time to project the inner component at `Y : Obj(A)`.

3) Then evaluate further at a general arrow `f : Obj(Hom_cat A X Y)` to obtain the
   *subscripted* component-at-arrow datum:
   - the outer index is already `X` (superscript),
   - so `f` is the inner/subscript index (as an arrow from `X` to `Y`).

This is the intended “nested components” story:

`ϵ` ↦ (outer transfor in `X`) ↦ (inner transfor in `Y`) ↦ (action at an arrow `f : X→Y`).

Importantly, this is **not circular**: we do not use `tapp1_*` to define inner components; we use
`tapp0_*` (already present) as the primitive evaluator.

### 1.3 Optional: packaging for hom-action (`tapp1_fapp1_func5`)

In the file, the `tapp1_fapp1_func` layer provides the hom-action of `tapp1_func_funcd`
on modifications (3-cells):

`fapp1_func (tapp1_func_funcd ...) ϵ ϵ' ↪ tapp1_fapp1_func ... ϵ ϵ'`.

For the “more internal” `tapp1_func_funcd5`, the analogous goal is:

- `tapp1_fapp1_func5` repackages a modification
  `α : Obj(Hom_cat (Transf_cat F G) ϵ ϵ')`
  into a modification between the outer transformations
  `fapp0 (tapp1_func_funcd5 F G) ϵ` and `fapp0 (tapp1_func_funcd5 F G) ϵ'`.

This is the “component-of-components” map at the modification level, mirroring the existing pattern.

---

## 2) Dependent case: `homd_cov5` and `tdapp1_func_funcd5`

The dependent part is where `homd_cov` matters. The key design decision in this plan is:

- do **not** try to eliminate the base `X_Z : Obj(Z)` binder everywhere at once;
  keep it external if needed for typability/performance,
  but internalize the relevant outer indices using nested `Transfd_cat` / projections (`tdapp0_*` + `tapp0_*`).

### 2.1 More-internal dependent hom (high-level goal)

We want an internalized version `homd_cov5` built functorially from:

- `hom_cov_func (Id_Z) : Z^op ⇒ (Z ⇒ Cat)`,
- a pointwise opposite-on-values operation `op2_Z` (derived from `op : Cat⇒Cat` by internal postcomposition),
- a fully-internalized pointwise product on Cat-valued functors:
  `prod_func5 : (Z⇒Cat) ⇒ (Z⇒Cat) ⇒ (Z⇒Cat)`,
- an internalized Grothendieck total operator:
  `Total_Z : (Z⇒Cat) ⇒ Cat`,
- and a fibration classifier `Fib` with consistent variance (either `Cat^op⇒Cat` or `Cat⇒Cat^op`,
  but chosen so the composites typecheck).

The intention is that the old “external parameter” `W_Z : Obj(Z)` becomes the **outer index**
of a functor out of `Z^op` (i.e. it is internalized exactly the way `hom_cov_func` internalizes `W`).

There are two equivalent viewpoints:

- (Functor-valued / strict Grothendieck) work with `E : Obj(Functor_cat Z Cat_cat)` and build
  a target `Z^op ⇒ Cat_cat` and then a transfor into it.
- (Displayed / slice) work with `E : Catd Z`, take `Op_catd E : Catd(Z^op)`, and map into a Grothendieck
  displayed category `Fibration_catd(...) : Catd(Z^op)`.

### 2.2 Interaction with `tdapp1` (nested projection story)

For the displayed analogue, the new target shape should be nested in the same way as the ordinary case:

- `tdapp1_func_funcd5` should map `ϵ : Obj(Transfd_cat FF GG)` to an outer transfor
  whose outer index is a displayed object (the “pair” `(X_,X)` in fibre language).

Operationally, components are then accessed by projections:

1) Apply `tdapp0_*` once to project the **outer** component (indexed by the displayed object over `X_Z`).

2) Apply `tapp0_*` once to project the **inner** component at the appropriate base/index object of the
   “simplex base” (e.g. an object of a total category encoding `E ×_Z hom(X_,−)` in the current draft intuition).

This is the key “two-level projection” story:

- displayed projection handles the outer (fibre) index,
- ordinary projection handles the inner (base/simplex) index.

As with the ordinary case, this is not circular: the projections `tdapp0_*` and `tapp0_*` are used to
extract components, not `tdapp1_fapp1_func`.

### 2.3 Corresponding `tdapp1_fapp1_func5`

Analogously to `tapp1_fapp1_func5`, the dependent `tdapp1_fapp1_func5` is the hom-action on displayed
modifications, repackaging:

- `α : Obj(Hom_cat (Transfd_cat FF GG) ϵ ϵ')`

into a displayed modification between the outer transformations yielded by `tdapp1_func_funcd5`.

---

## 3) Engineering plan / handover (next coding agent)

This section is a concrete plan for implementing the “more internal” version incrementally while
keeping `make check` working.

### Step A — Introduce internal postcomposition (derived from `comp_func` + currying)

Add a stable-head “postcompose on functor categories” helper (or derive it from a curried form of
`comp_func` specialized to `Cat_cat`) so we can define:

- `op2_Z : Obj(Functor_cat (Functor_cat Z Cat_cat) (Functor_cat Z Cat_cat))`
  with `fapp0 op2_Z F ↪ comp_func_cat op F`.

### Step B — Introduce a fully internalized pointwise product functor

Package `prod_func` as a curried functor object:

- `prod_func5 : Obj(Functor_cat (Functor_cat Z Cat_cat)
                    (Functor_cat (Functor_cat Z Cat_cat) (Functor_cat Z Cat_cat)))`

with β-rule `fapp0 (fapp0 prod_func5 D) E ↪ prod_func D E`.

### Step C — Introduce internalized Total and Fib (types first, computation later)

Add stable-head functor objects:

- `Total_Z : Obj(Functor_cat (Functor_cat Z Cat_cat) Cat_cat)`
  with object β-rule `fapp0 Total_Z M ↪ Total_cat (Fibration_catd M)`.

- `Fib` with a consistent variance convention:
  pick one and stick to it so `Fib ∘ Total ∘ ...` typechecks.

### Step D — Define `homd_cov5` using only functor composition

Define `homd_cov5` as either:

- a displayed morphism over `Z^op` (preferred if we keep `E : Catd Z`):
  `homd_cov5 : Obj(Functor_cat (Functord_cat ...) ...)` style, or
- a strict transfor (if committing to `E : Z⇒Cat`).

The key requirement: `W_Z` must be internalized as the outer index of a functor out of `Z^op`.

### Step E — Define `tapp1_func_funcd5` (ordinary)

Implement:

- `tapp1_func_funcd5 F G : Obj(Functor_cat (Transf_cat F G) (Transf_cat H0 H1))`
  with `H0 := hom_cov_func (Id_func A)` and `H1 := (hom_cov_func G) ∘ F^op`.

Then add “sanity assertions” exercising the intended component extraction via `tapp0_*` twice.

### Step F — Define `tdapp1_func_funcd5` (displayed)

Mirror Step E in the dependent setting, using `homd_cov5` and ensuring that components are extractable
by `tdapp0_*` followed by `tapp0_*`.

### Step G — Add the corresponding hom-actions (`*_fapp1_func5`)

Finally, add `tapp1_fapp1_func5` and `tdapp1_fapp1_func5` as the `fapp1_func`-parts of the new functors,
mirroring the existing β-rule pattern:

- `fapp1_func (tapp1_func_funcd5 ...) ϵ ϵ' ↪ tapp1_fapp1_func5 ... ϵ ϵ'`.
- similarly for the displayed case.

---

## 4) Notes and cautions

- Many of these “more internal” helpers should be introduced as *stable heads* (uninterpreted symbols
  + small β-rules) to keep rewriting robust and avoid conversion blowups.

- The nested `Transf_cat` / `Transfd_cat` approach is conceptually correct and not circular because
  components are accessed via `tapp0_*` / `tdapp0_*`, not via the `tapp1_fapp1_func*` layer.

