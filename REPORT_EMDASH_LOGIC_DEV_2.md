# REPORT — emdash2 logical development: `TotalΣ_cat` + `homd_cov_int_alt` (Incremental Path to Always-Σ `Total_cat`)

Date: 2026-02-07  
Repo: `/home/user1/emdash2`  
Target (future edits): `emdash2.lp`  

## Goal (restated)

We want `emdash2.lp` to support computational-logical omega-categories in Lambdapi, using rewrite/unification rules as the computational layer.

The specific design pivot addressed here:

1. Make the *total category* / comprehension `Total_cat` computational for **general** `E : Catd Z`, not only Grothendieck totals `E = Fibration_cov_catd M`.
2. Make the hom-categories of totals compute in a way that is compatible with the dependent hom classifier `homd_cov`, i.e.:
   - objects of `Total` are definitional Sigma pairs `(z,u)`,
   - morphisms between `(x,u)` and `(y,v)` are definitional Sigma pairs `(f, alpha)` where `f : x→y` and `alpha` is a displayed arrow over `f`.
3. Do this without destabilizing the development while infrastructure is incomplete, by introducing **parallel** symbols:
   - `TotalΣ_cat` as the intended always-Sigma total,
   - `homd_cov_int_alt` as the intended curried/internal formulation of dependent hom (related to the existing `homd_cov_int`).

Once stable, the plan is to migrate uses from `Total_cat` to `TotalΣ_cat`, then (optionally) delete/replace the legacy `Total_cat` computational shortcuts.

## Current state (what the kernel commits to today)

In `emdash2.lp`:

- `Total_cat [B] (E:Catd B) : Cat` exists for any `E : Catd B`, but computation is **special-cased**:
  - Objects compute to Sigma only for Grothendieck totals:
    - `τ (Obj (Total_cat (Fibration_cov_catd M))) ↪ Σ x:B, Obj(M x)`.
  - Homs compute only for Grothendieck totals:
    - `Hom_cat (Total_cat (Fibration_cov_catd M)) (x,u) (y,v)` reduces to an opposite of a Grothendieck total over `comp_hom_con_fib_cov`.
  - There are definitional collapses:
    - `Total_cat (Terminal_catd A) ↪ A`
    - `Total_cat (Lift_catd A) ↪ A`

- `homd_cov : ... → Functor (Total_cat(Product_catd ...)) Cat_cat` exists, with one key compute rule for the Grothendieck/Grothendieck case.
- `homd_cov_int` exists as an internal packaging (kept abstract).

This split is intentional: for general `Catd` (semantic isofibrations), transport along base arrows is not yet exposed computationally.

## Design decision: introduce an always-Sigma total in parallel

We introduce a second total constructor, **without modifying `Total_cat` initially**:

```lambdapi
symbol TotalΣ_cat [B : Cat] (E : Catd B) : Cat;
injective symbol TotalΣ_proj1_func [B : Cat] (E : Catd B) : τ (Functor (TotalΣ_cat E) B);
```

### Normalization on opposites (recommended; matches `Total_cat`)

`emdash2.lp` already normalizes totals-of-opposites *outwards* for `Total_cat`:

```lambdapi
rule @Total_cat _ (@Op_catd $B $E) ↪ Op_cat (@Total_cat $B $E);
```

For `TotalΣ_cat` we should mirror the same convention to avoid later “variance acrobatics” duplications:

```lambdapi
rule @TotalΣ_cat _ (@Op_catd $B $E) ↪ Op_cat (@TotalΣ_cat $B $E);
```

This is not logically required for Phase 1, but it is a cheap normalization rule that tends to reduce
the number of distinct normal forms we need to reason about.

### Object computation rule (always)

For *every* displayed category `E : Catd B`, objects of `TotalΣ_cat E` are definitional Sigma pairs:

```lambdapi
rule τ (Obj (@TotalΣ_cat $B $E))
  ↪ `τΣ_ x : τ (Obj $B), Obj (Fibre_cat $E x);
```

Notes:

- This rule should pattern-match in a way consistent with existing conventions around implicit base arguments (some heads use `_` on the base to avoid missed matches after dropping `injective Obj`).
- Use `Obj (Fibre_cat E x)` (a `Grpd` code) rather than `FibreObj` to keep the rule uniform with the Grothendieck object rule style. Either is acceptable, but choose one and keep it consistent.

### Projection computation on objects

```lambdapi
rule fapp0 (TotalΣ_proj1_func $E) (Struct_sigma $x $u) ↪ $x;
```

This provides the standard comprehension projection on objects without requiring any further structure.

## Hom computation: introduce a stable-head functor `TotalΣ_hom_func`

We want:

```
Hom_{TotalΣ E}((x,u),(y,v))  ≃  ∫_{f : x→y} (u →_f v)
```

where `(u →_f v)` is classified by `homd_cov` (or by a future internal/curried formulation derived from it).

### Engineering constraint

We should not attempt to directly implement a full definitional formula for the hom-category in terms of `homd_cov` immediately, because:

- it requires internal currying/evaluation infrastructure (to turn `homd_cov` into a functor on `Hom(x,y)^op`), and
- we want to control rewriting by stable heads to avoid conversion blowups and to keep rewrite orientation manageable.

### Proposed intermediate interface

Introduce:

```lambdapi
symbol TotalΣ_hom_func : Π [Z : Cat],
  Π (E : Catd Z),
  Π (x : τ (Obj Z)) (u : τ (FibreObj E x)),
  Π (y : τ (Obj Z)) (v : τ (FibreObj E y)),
  τ (Functor (Op_cat (Hom_cat Z x y)) Cat_cat);
```

Then define hom-categories of `TotalΣ_cat` in terms of Grothendieck totalization of this functor:

```lambdapi
rule Hom_cat (@TotalΣ_cat $Z $E) (Struct_sigma $x $u) (Struct_sigma $y $v)
  ↪ Op_cat (Total_cat (Fibration_cov_catd (TotalΣ_hom_func $E $x $u $y $v)));
```

Key points:

- This matches the already-established convention for Grothendieck homs:
  - `Hom_{∫M}` was defined as `Op_cat (Total_cat (Fibration_cov_catd ...))`.
- We keep `Op_cat` externally to enforce the chosen 2-cell direction convention (consistent with the existing Grothendieck opfibration story).
- The only new “semantic commitment” is that homs in `TotalΣ_cat` are implemented by *another* Grothendieck total. Computation is controlled by rewriting `TotalΣ_hom_func`, not by rewriting `Hom_cat` more deeply.

### First computation milestone: Grothendieck case

Provide a computation rule for `TotalΣ_hom_func` when `E = Fibration_cov_catd M`:

```lambdapi
rule TotalΣ_hom_func (@Fibration_cov_catd $Z $M) $x $u $y $v
  ↪ @comp_hom_con_fib_cov $Z $M $x $y $u $v;
```

Then:

`Hom_cat (TotalΣ_cat (Fibration_cov_catd M)) (x,u) (y,v)` reduces definitionally to the same shape already used by `Total_cat (Fibration_cov_catd M)`.

This allows incremental migration: any part of the codebase that relies on Grothendieck computations can move from `Total_cat` to `TotalΣ_cat` without losing definitional behavior (in the Grothendieck subcase).

## Internal currying/evaluation toolkit (minimal stable heads)

To express `TotalΣ_hom_func` for general `E` in terms of `homd_cov`/`homd_cov_int_alt`, we introduce two small stable heads.

### 1) Evaluation at an object as a functor object

We want a functor:

```
eval_x : Functor_cat(A,B) -> B
```

with the beta rule:

```
eval_x(F) = F(x)
```

Proposed:

```lambdapi
symbol eval0_func : Π [A B : Cat],
  τ (Obj A) → τ (Functor (Functor_cat A B) B);

rule fapp0 (eval0_func $x) $F ↪ fapp0 $F $x;
```

This enables internal compositions without expanding `fapp0` chains everywhere.

### 2) Internal Pi/sections over `Catd`

We want to internalize the “sections” view:

```
Pi(Z)(E) = Functord_cat(Terminal_catd Z, E)
```

as a functor object in `Cat_cat`.

Proposed:

```lambdapi
symbol Pi_func : Π (Z : Cat), τ (Functor (Catd_cat Z) Cat_cat);
rule fapp0 (Pi_func $Z) $E ↪ Functord_cat (Terminal_catd $Z) $E;
```

This matches the style of `Total_func`, `Fibration_cov_func`, `Fib_func`, `Catd_func`, etc.

## `homd_cov_int_alt`: intended role and interface

### Intended mathematical content

We want the “curried” formulation of the dependent hom classifier:

```
homd_cov_int_alt :
  Π z, (E[z])^op -> Π z', Hom_Z(z,z')^op -> (E[z'] -> Cat[z'])
```

This is logically equivalent to the existing uncurried form that takes a Sigma-total argument (a “triangle with a chosen target fibre object and base edge”).

### Engineering role

We do **not** need `homd_cov_int_alt` to compute for general `E : Catd Z` immediately.
We need:

- a stable head with a usable type that can be composed with:
  - `Pi_func`,
  - `eval0_func`,
  - functor category constructors (and eventually `Functor_catd`/`Functor_catd_func`),
- and later, computation rules that fire in the Grothendieck probe situation (where `E = Fibration_cov_catd E0`).

### Proposed approach

1. Introduce `homd_cov_int_alt` as a symbol with a type expressed as a composition of existing stable-head internal functors.
2. Do not add general computation rules yet.
3. Add computation rules only for the Grothendieck/Grothendieck case (mirroring the existing `homd_cov` pointwise rule), ensuring they reduce to:

```lambdapi
Hom_cat (E0 z)
  (E0(f)(W))
  (FF_z(d))
```

when all inputs are Grothendieck.

This is consistent with the “computational probe discipline” already used in `homd_cov_int`:
the final symbol is abstract, but key pointwise reductions exist in the concrete Grothendieck subcases.

Implementation note (important for typing):

- In `emdash2.lp`, `Fibration_con_catd [A] (F : A ⟶ Catᵒᵖ)` has type `Catd (Op_cat A)` (it flips the base).
- Therefore, if we build the “(z,v) ↦ Functor_cat((Hom_Z(W_Z,z))ᵒᵖ, Cat)” family via `Fibration_con_catd`,
  and we want it as a displayed category over the original base `A`, we must wrap it by `Op_catd`:

  `Op_catd (Fibration_con_catd ...) : Catd A`.

## Normalization and confluence discipline

The user intent is to add rules like:

- category-level: `Product_cat C Terminal_cat ↪ C`, `Product_cat Terminal_cat C ↪ C`,
- object-level: `Obj (Product_cat C Terminal_cat) ↪ Obj C`, etc.,
- and similarly “Sigma with unit” simplifications as needed.

This can resolve overlaps that would otherwise appear when we later make `Total_cat` always-Sigma.

However, the rewrite layer must still avoid the most common termination traps:

1. Avoid global eta/cancellation rules on `τΣ_` (decoded Sigma type) unless extremely carefully scoped.
   - Prefer categorical/product-level normalization and specialized `Obj`/`Hom_cat` shortcuts.
2. Keep stable heads, and fold toward them (existing pattern: `tapp0_fapp0`, `Fibre_func`, `Fibration_cov_fapp1_func`, etc.).
3. Prefer rules that reduce *structure* (`TotalΣ_cat`, `TotalΣ_hom_func`) rather than rules that expand arbitrary terms.

In practice, this suggests:

- Use `TotalΣ_cat` as the always-Sigma arena.
- Keep `Total_cat` (legacy) computations until migration is mostly complete.
- Only once the rewrite system is stable (and `make check` stays within timeout) consider:
  - switching `Total_cat` object computation to always-Sigma,
  - replacing legacy collapses (`Total_cat (Lift_catd A) ↪ A`) by derived equivalences or by additional normalization rules that make the two normal forms join.

### Note on “Sigma with unit” normalization

If/when we later want `Total_cat` itself to become always-Sigma on objects, we will need joinability between:

- legacy collapses like `Total_cat (Lift_catd A) ↪ A`, and
- the always-Sigma normal form `Σ (_:Obj(1)), Obj(A)`.

The user intent is to add rewrite rules such as `Product_cat C Terminal_cat ↪ C` (and similar), and to
add other rules to normalize away redundant “unit factors”.

Engineering recommendation:

- First add *category-level* normalizations (`Product_cat _ Terminal_cat ↪ _`, etc.) and any *targeted*
  `Obj`/`Hom_cat` shortcuts needed for those exact shapes.
- Delay global eta/cancellation rules on decoded Sigma (`τΣ_`) unless they can be scoped to a stable head
  (to avoid nontermination).

This keeps the rewrite system closer to the existing emdash2 style: normalize by stable-head constructors,
not by generic “algebraic simplification” on decoded types.

## Proposed incremental implementation plan

### Phase 0: baseline safety checks

- Keep using short timeouts during early rewrite work:
  - `EMDASH_TYPECHECK_TIMEOUT=60s make check`
- If a hang appears, investigate critical pairs and decision trees:
  - `lambdapi decision-tree <Module>.<symbol>`

### Phase 1: introduce `TotalΣ_cat` (objects + projection)

Add:

- `TotalΣ_cat`, `TotalΣ_proj1_func`
- (recommended) outward normalization on opposites for `TotalΣ_cat`
- object Sigma computation rule
- projection on objects computation rule

Add a small sanity assertion:

```lambdapi
assert [B : Cat] (E : Catd B) (x : τ (Obj B)) (u : τ (FibreObj E x)) ⊢
  fapp0 (TotalΣ_proj1_func E) (Struct_sigma x u) ≡ x;
```

### Phase 2: introduce hom shape via `TotalΣ_hom_func`

Add:

- `TotalΣ_hom_func` stable head
- `Hom_cat (TotalΣ_cat E) ...` rewrite to `Op_cat (Total_cat (Fibration_cov_catd (TotalΣ_hom_func ...)))`

Do not add computation for `TotalΣ_hom_func` yet.

### Phase 3: Grothendieck computation for `TotalΣ_hom_func`

Add the specialization:

- `TotalΣ_hom_func (Fibration_cov_catd M) ... ↪ comp_hom_con_fib_cov ...`

Sanity assertions:

- For Grothendieck `E`, homs in `TotalΣ_cat E` normalize to the same Sigma-object story already used for `Total_cat (Fibration_cov_catd M)`.

### Phase 4: add `eval0_func` and `Pi_func`

Add:

- `eval0_func` + beta rule
- `Pi_func` + beta rule

Sanity: ensure beta rules fire by definitional equality.

### Phase 5: internalize pointwise functor categories (needed for fully internal `homd_cov_int_alt3*`)

Add the “pointwise functor category family” from `REPORT_EMDASH_LOGIC_DEV.md` (Option A):

- `Functor_catd` and its fibre computation rule.

Then add the **internalized functor-object** version (needed for combinator-style internal pipelines):

```lambdapi
constant symbol Functor_catd_func :
  Π (B : Cat),
  τ (Functor (Op_cat (Catd_cat B)) (Functor_cat (Catd_cat B) (Catd_cat B)));
```

with a β-rule (object-action) expressing the intended currying:

- `fapp0 (fapp0 (Functor_catd_func Z) E) D ↪ Functor_catd E D`.

Also add the pointwise transfor family if needed for later steps:

- `Transf_catd` and `Fibre_transf` (Option A).

### Phase 6: add lightweight abbreviations for clarity (no rewrites)

For readability/uniformity in *types* and *definitions* (but avoid using them in LHS patterns):

- `Fib_cat (Z : Cat) : Cat ≔ Functor_cat Z Cat_cat`
- `Pi_cat [Z : Cat] (E : Catd Z) : Cat ≔ Functord_cat (Terminal_catd Z) E`

Optional (to reduce the “Π vs section tension” in notation):

- `Fibre_func_alt : Π [Z] [E D] (FF : τ (Functord E D)), τ (Functord (Terminal_catd Z) (Functor_catd E D))`

so that `Fibre_func FF z` is derived (conceptually) from `fdapp0 (Fibre_func_alt FF) z Terminal_obj`.
This does **not** force the definitional equation `Functord E D ≡ Pi_cat (Functor_catd E D)`; it merely
provides an explicit section-view when convenient for internal reasoning.

### Phase 7: add `homd_cov_int_alt` (binder wrapper; convenience view)

Keep the binder-style wrapper as a *convenience* interface:

- `homd_cov_int_alt : Π W_Z, Π W, sections over TotalΣ_cat(E) ...`

This is useful for warm-ups and for stating intended equations, but it is not the final “fully internal”
pipeline.

### Phase 8: add a *fully internal* `homd_cov_int_alt3_base` and `homd_cov_int_alt3`

The key correction (vs an object-only rewrite for a new `..._base`) is:

- `homd_cov_int_alt3_base` should be a **definitional abbreviation built from functor objects / combinators**
  (so its functorial structure is present “internally”), not merely a symbol with only a `fapp0` rewrite.

Concrete engineering guideline:

- Prefer a *δ-definition* (using `≔` and `comp_cat_fapp0`) for `homd_cov_int_alt3_base` and its auxiliary
  functor-valued subexpressions, so that both `fapp0` and `fapp1_func` can reduce by generic computation rules
  for `comp_cat_fapp0` (rather than being stuck on an opaque constant).
- It is acceptable to introduce 1–2 small “stable head” helpers (e.g. postcomposition-by-`Fib_func`, or the
  contravariant Grothendieck constructor as a functor object) if they make the δ-definition readable and
  keep rewrite heads small, but do not revert to “object-only computation rules” for the main base.

In `emdash2.lp` we expect such auxiliary helpers to look like:

- `Fibpost_val_func` (postcompose by `Fib_func` at the functor-category level),
- `Groth_con_func` (contravariant Grothendieck + outward `Op_catd`, as a functor object),
- and an explicit intermediate `..._fam` functor that is then postcomposed by `Pi_func`.

Target shape (blueprint; names adjusted to the emdash2 kernel):

- `homd_cov_int_alt3_base : Π [Z] (E : Catd Z), τ (Functor (Op_cat Z) Cat_cat)`
- `homd_cov_int_alt3 : Π [Z] (E : Catd Z), τ (Functord (Op_catd E) (Op_catd (Fibration_cov_catd (homd_cov_int_alt3_base E))))`

And the intended definition of `homd_cov_int_alt3_base` is the “logic-manipulation” pipeline sketched by the user,
using internal combinators such as:

- `Pi_func`
- `eval0_func` (user’s `fapp0_eval_func`)
- `Functor_catd` and `Functor_catd_func`
- `Fibration_cov_func`
- `op_val_func`, `hom_cov_int`

### Phase 9: define `TotalΣ_hom_func` as an abbreviation via `homd_cov_int_alt*` (plus optional Groth shortcut)

Target principle (from this report):

- `TotalΣ_hom_func E x u y v` should be a suitable specialization/evaluation of the internal dependent-hom pipeline,
  so the Grothendieck case computes because the pipeline computes.

Important refinement (from later review):

- If we keep a separate warm-up symbol `TotalΣ_hom_func_alt`, it should be a **definitional abbreviation**
  (a `symbol ... ≔ ...`) rather than a “folding rewrite rule” that makes `TotalΣ_hom_func_alt` a stable head.
  The stable-head discipline is still useful for big categorical constructors, but here the goal is precisely
  to expose the specialization/evaluation shape so it computes as the underlying pipeline computes.

Engineering allowance:

- keep (or reintroduce) a Grothendieck-specific computation rule for `TotalΣ_hom_func (Fibration_cov_catd M) ...` as a
  **confluent shortcut**, once joinability with the pipeline is visible (via `assert` sanity equalities).

### Phase 6: connect `TotalΣ_hom_func` to `homd_cov_int_alt`

Define (by rewrite or by a definitional abbreviation, depending on subject-reduction constraints) that:

- `TotalΣ_hom_func E x u y v` is computed as a suitable specialization/evaluation of `homd_cov_int_alt`.

Initially, this may only be done in the Grothendieck probe case to keep computation contained.

### Phase 7: migration and eventual replacement of `Total_cat`

Once `TotalΣ_cat` is stable and widely used:

1. Move call-sites of general “Σ-object reasoning” from `Total_cat` to `TotalΣ_cat`.
2. Add normalization rules (products with terminal, unit Sigma cancellations) needed to make the rewrite system robust.
3. Optionally redefine `Total_cat` to become definitionally equal to `TotalΣ_cat`, and delete legacy specialized computations.

## Expected outcome

This plan gives:

- an always-Sigma total construction usable today (`TotalΣ_cat`) without destabilizing legacy rules,
- a hom computation architecture that is:
  - definitional in shape,
  - computational in the Grothendieck subcase immediately,
  - extensible to the general semantic `Catd` case once `homd_cov_int_alt` and internal currying tools mature,
- a clean migration path toward the “always-Sigma `Total_cat`” future without forcing a single disruptive refactor step.

## Update (2026-02-07): `homd_cov_int_alt` vs “fully internal” and interaction with `TotalΣ_hom_func`

After implementing Phases 1–4 and adding a first version of:

- `homd_cov_int_alt : Π W_Z W, sections over TotalΣ_cat(E) ...`,

we identified a useful refinement of the plan, and a key overlap risk.

### 1) Warm-up: connect homs via `TotalΣ_hom_func`, not by rewriting `Hom_cat` directly

The architectural hook for hom computation is the stable head:

- `TotalΣ_hom_func E x u y v : (Hom_Z(x,y))ᵒᵖ ⟶ Cat`.

If we want “homs in `TotalΣ_cat` reduce to something involving `homd_cov`”, the right place to plug
the computation is a rewrite/definition for `TotalΣ_hom_func`, not the `Hom_cat (TotalΣ_cat ...)` rule.

### 2) Overlap/joinability risk with the Grothendieck computation rule

`TotalΣ_hom_func` already has a specialized computation rule for the Grothendieck probe case:

- `TotalΣ_hom_func (Fibration_cov_catd M) ... ↪ comp_hom_con_fib_cov ...`.

Long-term target (preferred): `TotalΣ_hom_func` should be *expressed in terms of* a fully internal
pipeline (here renamed `homd_cov_int_alt3*`), and then the Grothendieck computation should follow because
that pipeline computes when `E = Fibration_cov_catd M`.

However, during incremental development it is acceptable (and often desirable) to keep the above
Grothendieck-specific rule as a **confluent shortcut**, provided we verify joinability with the
eventual “definition via `homd_cov_int_alt3*`” (e.g. by `assert` sanity terms once the join is expressible).

In particular, we do not necessarily need an extra symbol like `TotalΣ_hom_func_from_alt` if we keep:

- one general-definition path (via `homd_cov_int_alt2`), and
- one Grothendieck shortcut path,

and we can later show they normalize to the same term in the Grothendieck case.

Adding a general rewrite (too early)

- `TotalΣ_hom_func E ... ↪ (fdapp0 (homd_cov_int_alt ...) (Struct_sigma y v) Terminal_obj)` (schematically),

would overlap when `E = Fibration_cov_catd M`. If `homd_cov_int_alt*` is still abstract in that case,
the overlap may not be joinable yet and risks breaking robustness. Hence the staging discipline:
delay the general rewrite until `homd_cov_int_alt3*` is computational enough that joinability is visible.

### 3) “Fully internal” `homd_cov_int_alt3*`: recommended staging

The current `homd_cov_int_alt` still has external Lambdapi binders:

```lambdapi
Π (W_Z : τ (Obj Z)),
Π (W : τ (FibreObj E W_Z)),
```

From a global “internalization” perspective, we want those to be supplied by `fdapp0` application
of an internal object (as in the style of `homd_cov_int`).

Recommendation:

1. Introduce `homd_cov_int_alt3` as a stable head that is *fully internal* (no explicit `W_Z`, `W` binders),
   supported by a definitional-abbreviation base `homd_cov_int_alt3_base` built from combinators (analogous
   in spirit to `homd_cov_int_base`).
2. Derive the current convenient binder form `homd_cov_int_alt` from `homd_cov_int_alt3`
   (definition or fold rule), so the external binder variant becomes a wrapper/view.
3. Implementing `homd_cov_int_alt3_base` *is* the “generic internal combinator” approach: it should be written
   directly as a composition of functor objects (requiring `Functor_catd_func`, `Pi_func`, `eval0_func`, etc.),
   so that the functorial structure is internal rather than being left as an uninterpreted constant.

### 4) Relation to `Functor_catd` / `Transf_catd` (Option A)

The “fully internal” blueprint you sketched uses pointwise functor-category families over `Z` and their
internal combinators. Independently, `REPORT_EMDASH_LOGIC_DEV.md` proposes adding:

- `Functor_catd`, `Transf_catd`, and `Fibre_transf` (fibrewise-only constructors),

to support “partial discharge” surface syntax.

Clarification:

- These additions are *not* merely orthogonal “syntax sugar” once we aim to make `homd_cov_int_alt3*`
  internal and inter-derivable (on-par) with the existing `homd_cov_int`.
- In practice, the same internal toolkit is reused across both developments:
  - internalized “Π/sections” operators (like `Pi_func`),
  - evaluation/currying operators (like `eval0_func`),
  - and pointwise functor-category families (`Functor_catd` and its internalized functor-object forms).

So, while Option A still avoids the strong definitional equation “displayed functor = section”, it is
expected that the *availability* of `Functor_catd`-level structure (and especially `Functor_catd_func`)
becomes a prerequisite for expressing the fully-internal `homd_cov_int_alt3*` pipeline in a reusable,
“logic-manipulation” style.

### 5) Updated next-step order (implementation)

Next implementation turn should proceed in this order:

1. Implement Option A (`Functor_catd`, `Transf_catd`, `Fibre_transf`) as fibrewise constructors (per `REPORT_EMDASH_LOGIC_DEV.md`).
2. Add `Functor_catd_func` (internalized functor-object form of `Functor_catd`) and any small abbreviations needed in types.
3. Add `homd_cov_int_alt3_base` (as a definitional abbreviation from combinators) and `homd_cov_int_alt3` (fully internal),
   plus a wrapper/derivation back to `homd_cov_int_alt`.
4. Define `TotalΣ_hom_func` (or an explicit alias) via specialization/evaluation of the `homd_cov_int_alt3*` pipeline,
   keeping any Grothendieck-specific rewrite as an optional shortcut once joinability is visible.
   (separate symbol or `assert`), without weakening the existing Grothendieck computation rule.
