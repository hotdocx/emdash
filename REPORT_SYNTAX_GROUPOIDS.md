# REPORT_SYNTAX_GROUPOIDS.md

Handover report (emdash2) consolidating the current design decisions about:

- surface type-theoretic syntax vs. internal Lambdapi kernel symbols,
- variance (functorial / natural / contravariant / object-only),
- groupoid aspects (`Obj : Cat → Grpd`) and the intended univalence story.

This file is meant to let a future AI coding agent continue the docstring/elaboration task without
having to reconstruct the discussion.

## 0. Context / goal

The repo currently implements the *kernel* of the emdash programming language inside Lambdapi
(`emdash2.lp`), as a computational specification for ω-category-theory inspired “functorial
programming”.

We want to **add docstrings/comments** mapping internal Lambdapi symbols to a **surface syntax**
that looks like traditional dependent type theory, with one crucial discipline:

- some variables are meant to *vary functorially*,
- some dependencies are *contravariant*,
- some are *natural* (in the emdash sense, via “transfors”),
- some are *object-only* (no implicit transport along base arrows).

The *variance is carried by the binder notation itself* in the surface language, not by explicitly
stating naturality laws in typing rules.

Operational semantics / reduction rules are discussed separately (later); the surface typing
notations already imply variance, while Lambdapi rewrite rules implement computation.


## 1. Surface binder modes (variance discipline)

We will use distinct binder forms in surface judgments.

### 1.1 Functorial binder

`z : Z ⊢ ...`

Meaning: `z` is a functorial index; the thing depending on `z` is (morally) an object of a functor
category, e.g. `E0 : Obj(Functor_cat Z Cat_cat)`.

This binder is used when functoriality is “real” and comes from typing in `Functor_cat`.

### 1.2 Contravariant binder

`x :^- A ⊢ ...`

Meaning: `x` is contravariant; the dependence is through an `Op_cat`-like mechanism, but we prefer
the lighter binder notation `:^-` over writing `A^op` at the surface level.

This is especially important for “accumulation”/composition laws for arrow-indexed components such
as `ϵ_(f)` (see `tapp1_fapp0` in `emdash2.lp`).

### 1.3 Object-only binder (preferred notation)

`z :^o Z ⊢ ...`

Meaning: `z` is *object-only*: you may substitute along paths/equality in `Obj Z` (groupoid-level),
but **you do not** assume any implicit transport along *base arrows* `f : z → z'` in `Z`.

This is the default binder for variables ranging over `Catd Z` data (displayed categories) when no
functorial structure is provided.


## 2. Silent coercions / elaboration policy (“τ-like” behavior)

Many internal kernel symbols will become silent/baked-into elaboration and surface notations (like
Lambdapi’s `τ` is already mostly silent).

Key policy decision:

### 2.1 Silent Grothendieck coercion for functorial families

If the user starts from a functorial family:

- `E0 : Obj(Functor_cat Z Cat_cat)` (surface: `z : Z ⊢ E[z] : Cat`)

then forming the displayed category

- `Fibration_cov_catd E0 : Catd Z`

is **silent** at the surface level: we reuse the same letter `E` and keep the same functorial binder:

- still write: `z : Z ⊢ E[z] : Cat`

even though “morally” `E` has become a displayed category `Catd Z`.

### 2.2 For a raw displayed category, use object-only binder

If we start directly with

- `D : Catd Z`

then we write

- `z :^o Z ⊢ D[z] : Cat`

because generic `Catd` does not (yet) provide functorial reindexing along base arrows.


## 3. Prototype surface readings (examples)

### 3.1 Functors

Internal:

- `Functor_cat : Π (A B : Cat), Cat`
- `F : Obj(Functor_cat A B)`

Surface reading:

- `⊢ A : Cat`
- `⊢ B : Cat`
- `x : A ⊢ F[x] : B`

(`x:A` indicates functorial variation; no additional “preservation laws” are stated at the surface
typing level.)

### 3.2 Displayed functors (fibrewise reading)

Internal:

- `Functord_cat : Π [Z : Cat], Π (E D : Catd Z), Cat`
- `FF : Obj(Functord_cat E D)`

Surface reading:

- `⊢ Z : Cat`
- `z :^o Z ⊢ E[z] : Cat`
- `z :^o Z ⊢ D[z] : Cat`
- `z :^o Z, e : E[z] ⊢ FF[e] : D[z]`

This is a “dependent function on fibre objects” reading, with `z` *not* assumed functorial.

### 3.2b. Simplicial / “over a base arrow” displayed morphisms (Grothendieck-style)

We use the notation:

- `f : z → z'` for a base 1-cell in `Z`,
- `σ : e →_f e'` for a displayed 1-cell in `E : Catd Z` lying over `f`,
  where `e : E[z]` and `e' : E[z']`.

This is the simplicial/Grothendieck notion of “a morphism over a base edge” used throughout `emdash2.lp`
(2-simplex / 3-simplex intuition).

### 3.3 Transfors: object-indexed vs arrow-indexed components

Internal:

- `Transf_cat : Π [A B], Π (F G : Obj(Functor_cat A B)), Cat`
- `ϵ : Obj(Transf_cat F G)`

Surface facade (NOT a projection rule; just the meaning of `ϵ : Obj(Transf_cat F G)`):

- `⊢ A : Cat`
- `⊢ B : Cat`
- `x : A ⊢ F[x] : B`
- `x : A ⊢ G[x] : B`
- `x : A ⊢ ϵ[x] : F[x] → G[x]`

Arrow-indexed (“profunctorial”) component is explicit in the surface language (prototype):

Internal stable head:

- `tapp1_fapp0 : ... → (f : Hom_A x y) → Hom_B(F x, G y)`

Surface:

- `x :^- A, y : A, f : x → y ⊢ ϵ_(f) : F[x] → G[y]`

The contravariant accumulation in `x :^- A` is reflected computationally by rewrite rules such as:

- postcomposition-side accumulation: `(G g) ∘ ϵ_(f) ↪ ϵ_(g∘f)`
- precomposition-side accumulation: `ϵ_(f) ∘ (F g) ↪ ϵ_(f∘g)`

In `emdash2.lp` these are currently implemented as Phase-2 “strict naturality” rewrite rules for the
stable head `tapp1_fapp0`.

### 3.4 Dependent-hom (simplicial) syntax: `homd_cov_int`

Kernel symbol (simplified):

- `homd_cov_int : (D0 : Z ⟶ Cat), (FF : (∫D0) ⟶_Z E) ⟼ (Op_catd E) ⟶_Z ...`

Surface reading for `σ : homd_cov_int ...`:

```
Z : Cat
E : Catd Z
D0 : (z:Z ⊢ D0[z] : Cat)
FF : (z:^o Z, d:D0[z] ⊢ FF[d] : E[z])

z:^o Z, e:E[z], z':Z, f:z→z', d:D0[z'] ⊢ σ : e →_f FF[d]
```

Note the binder correction: because `E` forces `z:^o Z` (object-only) in the surface language,
we write the `FF` fibrewise typing with `z:^o Z` as well, even though `D0` itself varies functorially.

### 3.5 Displayed transfors: simplicial arrow-indexed components via `tdapp1_int_fapp0_transfd`

For `ϵ : Transfd_cat FF GG`, the diagonal component is already covered by the classifier reading:

`z:^o Z, e:E0[z] ⊢ ϵ[e] : FF[e] → GG[e]`

What we need explicitly (analogue of ordinary `ϵ_(f)`) is the “over-a-base-arrow” component:

```
z:^o Z,
e  : E0[z],
z' : Z,
f  : z → z',
e' : E0[z'],
σ  : e →_f e'
⊢
ϵ_(σ) : FF[e] →_f GG[e']
```

This is the surface reading of the internal packaging `tdapp1_int_fapp0_transfd` (and related `tdapp1_int_*` family),
which turns a displayed transfor into its simplicial/off-diagonal components indexed by displayed arrows over `f`.


## 4. Groupoids and “univalence”: current understanding

### 4.1 Current kernel fact

`emdash2.lp` has:

- `Obj : Cat → Grpd`

so “object variables” live in a groupoid-like universe (`Grpd`), and we have paths/equality:

- `x = y : Grpd` for `x,y : τ(Obj C)`.

### 4.2 Path_cat (a.k.a. “discrete/groupoidal category” in our terminology)

We use “discrete” to mean “groupoid”, i.e. a category whose homs are paths (not the set-theoretic
discrete category with empty homs).

We want a Cat-constructor:

- `Path_cat : Grpd → Cat`

with definitional behavior:

- `Obj(Path_cat A) ≡ A`
- `Hom_cat(Path_cat A) x y ≡ Path_cat (x = y)`
- `id` and `comp_fapp0` computed by reflexivity and path composition

This is infrastructure independent of univalence.

### 4.3 isEquiv / equivalence in ω-categories (independent of univalence)

We need a good notion of “equivalence/isomorphism” for 1-cells in ω-categories, proof-relevant and
recursive (left/right inverses may differ; higher witnesses exist).

Two acceptable shapes were discussed:

#### Option A (external family)

- `isEquiv : Π C x y, (f : Obj(Hom_cat C x y)) → Grpd`

#### Option B (preferred internal integration)

Package `isEquiv` as a displayed category over the hom-category:

- `isEquiv : Π [C:Cat] [x y:Obj C], Catd (Hom_cat C x y)`

Then, for each base arrow `f : Obj(Hom_cat C x y)`, a *witness* that `f` is an equivalence is an
object in the fibre:

- witness type: `Obj(Fibre_cat (isEquiv C x y) f)`

And “a choice of witness for every f” is a **section** of the displayed category:

- `section : Obj(Functord_cat (Terminal_catd (Hom_cat C x y)) (isEquiv C x y))`

This representation fits the emdash2 “internal story” better (sections/probes, Grothendieck totals,
etc.), and it does not assume fibres are groupoids/propositions upfront (that can be proved later).

### 4.4 Univalence principle (later, global)

Goal: “equivalences in C ARE paths in Obj C”, as computational/definitional as possible.

We will likely implement this with **one rewrite direction + one unification direction** to avoid
rewrite loops:

- canonical direction (rewrite): paths → (arrow + equivalence witness)
- inverse direction (unif_rule): (equivalence witness) → path

We also want the path-to-arrow map packaged as a functor:

- `path_to_hom_func : Obj(Functor_cat (Path_cat (x = y)) (Hom_cat C x y))`

with pointwise `path_to_hom` recovered via `fapp0`.

The “isEquiv” witness for those arrows is provided by an additional symbol (separate stable head):

- `path_to_hom_isEquiv : Π p, Obj(Fibre_cat (isEquiv C x y) (fapp0 path_to_hom_func p))`

The other direction (“equiv witness → path”) is best as a unification rule or protected rewrite head.


## 5. Docstrings strategy (forthcoming implementation task)

We will annotate `emdash2.lp` symbols with surface judgments (TT-like), using the binder discipline
above (`:`, `:^-`, `:^o`).

Important constraint: docstrings should not introduce explicit “naturality proof terms”.
Functoriality/naturality/contravariance are implicit from binder forms; rewrite rules are separately
discussed as operational semantics.

### 5.1 Separation of concerns

- **Typing/formation docstrings**: “what this symbol means in surface syntax”.
- **Operational semantics section**: later, explain which rewrite rules implement reductions for the
explicit surface constructors (e.g. `ϵ_(f)` reduction/accumulation via `tapp1_fapp0` rules).

### 5.2 Explicit vs silent symbols

- Some internal projections (`fapp0`, `tapp0_fapp0`, etc.) are expected to become silent/baked-in.
- Some are explicit surface constructors with their own notation:
  - Σ-pairing and projections (`Struct_sigma`, `sigma_Fst`, `sigma_Snd` ↔ `⟨_,_⟩`, `π₁`, `π₂`)
  - arrow-indexed transfor component `tapp1_fapp0` ↔ `ϵ_(f)` (explicit; key example)


## 6. Immediate next steps (when code edits are allowed)

1. Add a short “binder legend / surface syntax conventions” section near the top of `emdash2.lp`
   referencing `:`, `:^-`, `:^o`, and the silent `Fibration_cov_catd` coercion.
2. Add surface-judgment docstrings for:
   - `Cat`, `Obj`, `Hom_cat`, `id`, `comp_fapp0`
   - `Functor_cat`, `fapp0`, `fapp1_*`
   - `Catd`, `Fibre_cat`, `Functord_cat`, `fdapp0`
   - `Transf_cat`, `tapp0_*`, `tapp1_fapp0`
3. (Infrastructure, later) Introduce `Path_cat`, and then define/document `Core_cat(C) ≔ Path_cat(Obj C)`.
4. (Infrastructure, later) Introduce `isEquiv` (preferred as `Catd(Hom_cat C x y)`), then univalence
   bridges using rewrite+unif split.

5. (Syntax, next) Add surface syntax docstrings for the simplicial layer:
   - `homd_cov_int` (σ : e →_f FF[d]),
   - `tdapp1_int_fapp0_transfd` (ϵ_(σ) : FF[e] →_f GG[e']).
