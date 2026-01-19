# OUTLINE: More-internal formulation (corrected) — `hom_cov_int` / nested `Transf_cat` / `homd_cov5`

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

- `hom_cov_int` (already internalizes `W`):
  - `hom_cov_int : Π [A] [B] (F : Obj(Functor_cat B A)), Obj(Functor_cat (Op_cat A) (Functor_cat B Cat_cat))`
  - with β-rule `fapp0 (hom_cov_int F) X ↪ hom_cov A X B F`.

So the “make `W` internal” step is already solved for `hom_cov`.

### Existing `tapp1_*` packaging (outer index is currently external)

Currently (simplified) the file has:

- `tapp1_func_funcd : Π X_A, Obj(Functor_cat (Transf_cat F G) (Functord_cat (FibrationOp_catd (hom_cov X id)) (FibrationOp_catd (hom_cov (F X) G))))`

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

Key observation: `hom_cov_int` already gives:

- for `Id_A : A⇒A`, a functor `H0 := hom_cov_int (Id_A) : A^op ⇒ (A ⇒ Cat)`.
- for `G : A⇒B`, a functor `hom_cov_int G : B^op ⇒ (A ⇒ Cat)`.

To get a functor of shape `A^op ⇒ (A ⇒ Cat)` from `hom_cov_int G`, precompose by `F^op`:

- `F^op : A^op ⇒ B^op` is `Op_func A B F`.
- define `H1 := (hom_cov_int G) ∘ F^op : A^op ⇒ (A ⇒ Cat)`.

Then the “more internal” `tapp1` target is:

```text
tapp1_func_funcd5 F G :
  Obj(Functor_cat (Transf_cat F G) (Transf_cat H0 H1)).
```

This is the correct replacement for earlier ill-typed attempts like
`FibrationOp_catd (hom_cov_int ...)` (those are ill-typed because `FibrationOp_catd` expects a functor
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

- `hom_cov_int (Id_Z) : Z^op ⇒ (Z ⇒ Cat)`,
- a pointwise opposite-on-values operation `op2_Z` (derived from `op : Cat⇒Cat` by internal postcomposition),
- a fully-internalized pointwise product on Cat-valued functors:
  `prod_func5 : (Z⇒Cat) ⇒ (Z⇒Cat) ⇒ (Z⇒Cat)`,
- an internalized Grothendieck total operator:
  `Total_Z : (Z⇒Cat) ⇒ Cat`,
- and a fibration classifier `Fib` with consistent variance (either `Cat^op⇒Cat` or `Cat⇒Cat^op`,
  but chosen so the composites typecheck).

The intention is that the old “external parameter” `W_Z : Obj(Z)` becomes the **outer index**
of a functor out of `Z^op` (i.e. it is internalized exactly the way `hom_cov_int` internalizes `W`).

There are two equivalent viewpoints:

- (Functor-valued / strict Grothendieck) work with `E : Obj(Functor_cat Z Cat_cat)` and build
  a target `Z^op ⇒ Cat_cat` and then a transfor into it.
- (Displayed / slice) work with `E : Catd Z`, take `Op_catd E : Catd(Z^op)`, and map into a Grothendieck
  displayed category `FibrationOp_catd(...) : Catd(Z^op)`.

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

### Step A — Introduce internal postcomposition using `comp_func` specialized to `Cat_cat` (curried)

Goal: define *functorial* postcomposition on functor categories, so that “pointwise opposite”
on Cat-valued functors becomes a genuine functor object (not merely a definitional abbreviation).

What we already have:

- `comp_func` (uncurried composition-as-functor) for any category `A : Cat`:
  - `comp_func A X Y Z : Obj(Functor_cat (Product_cat (Hom_cat A Y Z) (Hom_cat A X Y)) (Hom_cat A X Z))`
  - β-rule: `fapp0 (comp_func ...) (Struct_sigma g f) ↪ comp_fapp0 ... g f`.

Specialize to `A := Cat_cat`, where:

- objects of `Cat_cat` are categories,
- `Hom_cat Cat_cat B C ↪ Functor_cat B C` (already in `emdash2.lp`).

Then `comp_func Cat_cat X Y Z` is (definitionally) the composition functor:

- `Functor_cat Y Z × Functor_cat X Y → Functor_cat X Z`.

We want the *curried* postcomposition operator (stable head is fine):

```text
postcomp_cat :
  Π [X Y Z : Cat],
  τ (Obj (Functor_cat Y Z))
    → τ (Obj (Functor_cat (Functor_cat X Y) (Functor_cat X Z)))

β (objects):
  fapp0 (postcomp_cat G) F ↪ comp_fapp0 Cat_cat X Y Z G F
```

With this, define pointwise opposite-on-values for Cat-valued functors:

```text
op2_Z := postcomp_cat (X:=Z) (Y:=Cat_cat) (Z:=Cat_cat) op
       : Obj(Functor_cat (Functor_cat Z Cat_cat) (Functor_cat Z Cat_cat))
```

and `fapp0 op2_Z F ↪ comp_cat_fapp0 op F` computes by the β-rule above.

Note (general curry/uncurry mechanism):
This step is one instance of a broader interface we will likely want to introduce explicitly:
currying/uncurrying for functor categories, i.e. the usual bijection

- `Functor_cat (Product_cat X K) Z  ≃  Functor_cat X (Functor_cat K Z)`

(“`− × K` is left adjoint to `Functor_cat K −`” at the level of objects).
For the present goal, we can get away with the specific curried postcomposition operator above,
but later steps (notably internalizing “pointwise `op`” and other postcomposition/precomposition maps
as functors) become cleaner if we introduce general-purpose curry/uncurry stable heads.

### Step B — Introduce a fully internalized pointwise product functor

Package `prodFib` as a curried functor object:

- `prod_func5 : Obj(Functor_cat (Functor_cat Z Cat_cat)
                    (Functor_cat (Functor_cat Z Cat_cat) (Functor_cat Z Cat_cat)))`

with β-rule `fapp0 (fapp0 prod_func5 D) E ↪ prodFib D E`.

### Step C — Introduce internalized `Total_Z` and `Fib` (choose variance so compositions typecheck)

We want to build a functor `Op_cat Z → Cat_cat` from the pipeline
`hom_cov_int(id)` → `op2_Z` → `prod_func5` → `Total_Z`, and then optionally lift it to a “fibration classifier”
level via `Fib`.

#### (C1) Internalized Grothendieck total (object-level β-rule is enough initially)

Add a single (stable head) symbol `Total` parameterized by the base `Z`:

```text
Total :
  Π [Z : Cat],
  τ (Obj (Functor_cat (Functor_cat Z Cat_cat) Cat_cat))

β (objects):
  fapp0 (Total [Z]) M ↪ Total_cat (FibrationOp_catd M)
```

This makes `Total_Z` usable in functor composition inside `Cat_cat`.

#### (C2) Internalized fibration classifier (`Fib`) — pick a convention that composes cleanly

Semantics: “fibrations over B” should be the functor category `Functor_cat B Cat_cat`.
Functoriality in `B` is contravariant (pullback/precomposition).

We adopt the following convention because it composes cleanly with `Base : Op_cat Z → Cat_cat` and
keeps the “opfibration vs fibration” orientation explicit rather than relying on definitional shortcuts:

- `Fib : Cat_cat → (Op_cat Cat_cat)` as a functor object:

  ```text
  Fib :
    τ (Obj (Functor_cat Cat_cat (Op_cat Cat_cat)))

  object action (intended):
    fapp0 Fib B ↪ Functor_cat B Cat_cat
  ```

Given `Base : Obj(Functor_cat (Op_cat Z) Cat_cat)`, we then perform the explicit “op-acrobatics”
to obtain a displayed category over `Op_cat Z`:

1) Compose to get:
   - `Fib∘Base : Obj(Functor_cat (Op_cat Z) (Op_cat Cat_cat))`.

2) Apply `Op_func` to flip both domain/codomain:
   - `Op_func (Fib∘Base) : Obj(Functor_cat Z Cat_cat)`.

3) Grothendieck-totalize to a displayed category over `Z`:
   - `FibrationOp_catd (Op_func (Fib∘Base)) : Catd Z`.

4) Opposite the displayed category to get a displayed category over `Op_cat Z`:
   - `Op_catd (FibrationOp_catd (Op_func (Fib∘Base))) : Catd (Op_cat Z)`.

This final object is the target displayed category over `Op_cat Z` we will use in `homd_cov5`.

### Step D — Define `homd_cov5` explicitly (the consolidated formula)

This step records the consolidated “earlier approach” formula: internalize the former external
`W_Z : Obj(Z)` by making it the *outer index* of a functor out of `Op_cat Z`, exactly as `hom_cov_int`
already does for `hom_cov`.

Fix a base category `Z : Cat` and a Cat-valued functor (for computations) `D : Obj(Functor_cat Z Cat_cat)`
(in applications you can take `D` to be the Cat-valued data underlying a Grothendieck displayed category).

1) Start from the already internalized representable-in-context:

```text
HId := hom_cov_int (@id_func Z)
    : Obj(Functor_cat (Op_cat Z) (Functor_cat Z Cat_cat))
```

2) Apply pointwise opposite on values (postcompose inside `Cat_cat` by `op2_Z`):

```text
HOp := comp_cat_fapp0 op2_Z HId
    : Obj(Functor_cat (Op_cat Z) (Functor_cat Z Cat_cat))
```

3) Multiply pointwise by `D` using the fully internalized curried product:

Let `prodD := fapp0 prod_func5 D` so
`prodD : Obj(Functor_cat (Functor_cat Z Cat_cat) (Functor_cat Z Cat_cat))` and
`fapp0 prodD E ↪ prodFib D E`.

Then:

```text
HProd := comp_cat_fapp0 prodD HOp
     : Obj(Functor_cat (Op_cat Z) (Functor_cat Z Cat_cat))
```

4) Totalize pointwise (postcompose by `Total_Z`):

```text
Base := comp_cat_fapp0 (Total [Z]) HProd
     : Obj(Functor_cat (Op_cat Z) Cat_cat)
```

This `Base` is the “true functor” version of the former `W_Z ↦ Dom(W_Z)` story:
the old external parameter `W_Z` is now the object argument of `Base : Z^op → Cat`.

5) Lift to “fibration classifier level” (explicitly; no definitional shortcut):

```text
BaseFib := comp_cat_fapp0 Fib Base
       : Obj(Functor_cat (Op_cat Z) (Op_cat Cat_cat))
```

Then define the target displayed category over `Op_cat Z` as:

```text
Target :=
  Op_catd (FibrationOp_catd (Op_func BaseFib))
  : Catd (Op_cat Z)
```

Finally, the “displayed/slice form” is the one we keep (the strict-transfor attempt can be dropped):

```text
homd_cov5 :
  Π [E : Catd Z] [D : Catd Z] (FF : Obj(Functord_cat D E)),
  Obj(Functord_cat (Op_catd E) Target)
```

(In early phases one can take `D := E` and `FF := id_funcd` for intuition and to reduce typing noise.)

Key property: the former external `W_Z : Obj(Z)` is now internalized as the component index of
the outer base `Op_cat Z` (i.e. as part of `Op_catd E`), while `W_EW` is internalized as the
object argument of the resulting displayed functor on fibres.

### Step E — Define `tapp1_func_funcd5` (ordinary)

Implement:

- `tapp1_func_funcd5 F G : Obj(Functor_cat (Transf_cat F G) (Transf_cat H0 H1))`
  with `H0 := hom_cov_int (id_func A)` and `H1 := (hom_cov_int G) ∘ F^op`.

Then add “sanity assertions” exercising the intended component extraction via `tapp0_*` twice.

### Step F — Define `tdapp1_func_funcd5` explicitly (nested-`Transfd_cat`, non-circular)

We aim to “internalize the outer index” in the displayed analogue exactly as in the ordinary case:
the target should be a (displayed) transfor whose outer component index is a displayed/fibre object,
and whose inner component index is then accessed by `tapp0_*`.

Let `Z : Cat`, `E D : Catd Z`, and `FF GG : Obj(Functord_cat E D)`.

Then the “more internal” `tdapp1` should have the nested form:

```text
tdapp1_func_funcd5 FF GG :
  Obj(Functor_cat (Transfd_cat FF GG)
      (Transfd_cat (homd_cov5 id) ((homd_cov5 GG) ∘ (FF^op))))
```

where:

- `homd_cov5 id` denotes the “identity/special case” used on the source side (the analogue of `H0`),
- `homd_cov5 GG` denotes the target-side classifier depending on `GG`,
- `FF^op` is the appropriate “opposite/precomposition” on the outer index side (depending on which variant
  of `homd_cov5` is adopted: strict `Op_func` when `FF` is an ordinary functor, or the displayed analogue
  realized via `Op_catd`/pullback simulation when staying in `Catd`).

In our setting (keeping `Catd`), the intended meaning of `FF^op` is: interpret the “opposite on the outer base”
via the existing `Op_catd` infrastructure (and, when necessary, the pullback-simulation pattern already used
in `emdash2.lp`), so that the composite
`(homd_cov5 GG) ∘ (FF^op)` is a well-typed outer classifier over `Op_cat Z`.

Operational semantics (the important part):

- Given `ϵ : Obj(Transfd_cat FF GG)`, applying `fapp0` yields an *outer* displayed transfor.
- Apply `tdapp0_*` once to project the outer component at the displayed object (outer index).
- Apply `tapp0_*` once to project the inner component at the base/simplex index living in the
  “surface base” (typically a total category encoding `E ×_Z hom(X_,−)` in the intended semantics).

This “`tdapp0_*` then `tapp0_*`” projection sequence is the non-circular mechanism for accessing nested
components in the displayed setting.

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
