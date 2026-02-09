# REPORT_EMDASH_TYPESCRIPT_ELABORATION.md

This report consolidates the design discussion about **emdash2-style internal computational logic**
and how to reflect it in the **TypeScript kernel** (the v1 executable kernel in `emdash1/`), while
**ignoring string parsing** (i.e. not focusing on `emdash1/src/parser.ts`).

The key point is that emdash2’s `_int_` constructions are *not parsing conveniences*: they are
**new named discharge/abstraction operators of the type theory** whose rewrite theory makes
functoriality/naturality *computational*.

---

## 0. Scope and intent

We focus on:

- the **core term/kind design starting at** `emdash1/src/types.ts`,
- the role of **mode-annotated context binders** (variance / “how a variable may vary”),
- the meaning of emdash2’s `*_int_*` symbols as **explicit discharge/abstraction**,
- the functor/transfor fragment as the minimal blueprint to extend later (displayed categories,
  `homd_int`, etc.).

We explicitly do **not** focus on:

- surface syntax parsing choices,
- backward compatibility with the existing emdash1 categorical code (considered outdated).

---

## 1. Why “mere variable type” is not enough: we must remember *how* variables vary

In ordinary dependent type theory, “what a variable ranges over” is recorded by its type in the
context. For emdash2, this is insufficient because emdash2 has an additional discipline:

> the kernel must know whether a dependency is allowed to use **arrow-indexed action**
> (functorial/natural variation along a category), or only **object/path substitution**.

This is the purpose of emdash2 binder annotations:

- `x : A`     (functorial index)
- `x :^o A`   (object-only index)
- `x :^- A`   (contravariant / accumulation-friendly index)

Even if two binders have the same *underlying* object type (e.g. both are “objects of `A`”), they may
have different admissible eliminations/normalizations depending on whether they are functorial/natural
indices. This information must be carried by the **context/binders**, not by special `Var` nodes.

### 1.1. No `CVar` / `FVar`

We agreed that introducing special variable nodes like `CVar`/`FVar` is not the right move:

- “variable-ness” does not carry the semantics; the semantics comes from the binder/context discipline.

### 1.2. Yes: mode-annotated binders / context entries

We need to extend the kernel notion of binders/context entries with:

- a **binder mode** (e.g. `Functorial` / `ObjectOnly` / `Contravariant`), and
- crucially, the **controlling category of variation** (the category whose arrows govern the allowed
  arrow-indexed action).

This controlling category is typically:

- for `x :^nat A` (or `x : A` in emdash2 surface): the controlling category is `A`,
- for `f :^func x → y`: the controlling category is `Hom_cat A x y` (a `Cat`).

This is essential for internal “nested `Transf_cat`” constructions: after internalization,
new binders appear whose controlling category is not the original `A` but a derived hom-category.

---

## 2. `:^func` vs `:^nat`: what is the right decomposition?

We discovered an important distinction:

- **`:^func`** (functorial index) is a **standalone, primitive binder mode** for functorial variation.
  Intuitively: variables marked `:^func` may be acted on along arrows of their controlling category
  via stable-head arrow-action operators (functor hom-actions, etc.). This mode applies whenever a
  binder ranges over some index category `K : Cat` (including hom-categories like `Hom_cat A x y`).

- **`:^nat`** (natural index) is **independent of `:^func`** and is best understood as a
  **formation/intro (discharge) discipline for transformations/transfors**: it is what authorizes
  internal discharge of diagonal component families into a `Transf`.

In particular:

- `:^func` appears in off-diagonal constructions for transformations because the internalization
  packagers (e.g. `tapp1_int_func_transf`) produce *functors* whose domains are hom-categories; the
  arrow/cell argument `f` is then a functorial binder ranging over that hom-category.
  This does **not** make `:^func` derived from `:^nat`: `:^func` remains a standalone concept.

### 2.1. Accumulation/cut is *rewrite theory*, not the meaning of `:^func`

The “cut-accumulation” equations (exchange law normalizations, etc.) belong to the **rewrite theory of
off-diagonal stable heads** like `ϵ_(–)` (and later displayed analogues). They are not the reason a binder
is functorially annotated.

So we keep two separate ideas:

- binder-mode tells which *eliminations are admissible*;
- rewrite rules tell how those eliminations compute/normalize (accumulation included).

---

## 3. The key kernel interpretation: `*_int_*` are named discharge/abstraction operators

This is the main finding.

emdash2’s internal symbols like `tapp1_int_func_transf` are best understood as:

> explicit named operations in the kernel that **discharge structured, mode-annotated context fragments**
> into stable-head objects (typically functors or transfors), and whose computation is governed by rewrite rules.

They play the same “structural role” as Π/λ in ordinary type theory, but specialized to the
functorial/natural binder discipline.

### 3.1. Analogy: `MkFunctorTerm` in emdash1 is already a discharge operator

`emdash1/src/elaboration.ts` contains `infer_mkFunctor`, where `MkFunctorTerm`:

- accepts `fmap0` and `fmap1`,
- then checks the functoriality equation by normalization,
- and produces a functor object.

This is already a kernel-level “named discharge/intro” operator with computational coherence.

### 3.2. Missing sibling: a transfor discharge operator (intro for `Transf`)

To make `ϵ : Transf F G` a *bound variable* in contexts (as required by internal `tapp1_int_*`),
the TS kernel needs an intro/discharge operator for transfors, analogous to `MkFunctorTerm`.

Crucially, under the intended meaning of `:^nat`, **the user does not need to supply off-diagonal data**:

- intro takes only diagonal components under a `:^nat` binder, and
- off-diagonal components are *derived* by elimination/packaging operators (the `tapp1_int_*` pipeline).

---

## 4. The “off-diagonal” typing discipline (the corrected, internalization-aligned form)

We corrected a key point:

The off-diagonal component of a transfor has the form

```text
x :^nat A, y :^nat A, f :^func (x → y)  ⊢  ϵ_(f) : Hom B (F[x]) (G[y]).
```

Explanation:

- `x` and `y` are *natural indices* in `A`, because the object-indexed diagonal family
  `x :^nat A ⊢ ϵ[x] : Hom B (F[x]) (G[x])` is the data that can be discharged into `Transf F G`.
- `f` is `:^func` because (after nested internalization) the elimination pipeline produces a **functor**
  whose domain is the **hom-category** `Hom_cat A x y`, and `f` is an object of that category. Here `:^func`
  is used in its standalone sense (“binder varies functorially over its controlling category”).

So `:^func` on `f` means “argument to a functor object whose domain is `Hom_cat A x y`”.

---

## 5. The surface-level inconsistency: `ϵ_(f)` exists but `F₁(f)` is absent

We verified by inspection that:

- `docs/SYNTAX_SURFACE.md` explicitly says arrow-action `F[f]` is surface-silent and does *not* provide
  an explicit `F₁(f)` syntax.
- `emdash2.lp` contains comments emphasizing “no explicit `F[f]` term former”.
- `EMAIL.md` mentions both `FF₁(σ)` and `ϵ_(σ)` as intended surface notations.

This is an asymmetry. For conceptual uniformity, we want functor arrow-action and transfor off-diagonal
to sit in the same computational universe. In particular:

> `F₁(f)` can be understood as `(1_F)_(f)` where `1_F` is the identity transfor on `F`.

emdash2.lp itself comments about instantiating `tapp1_int_*` at identity transfors (e.g. “apply
`tapp1_int_func_transf` to the identity transfor `1_F`”), which supports this uniformity.

### 5.1. Consequence for TS kernel design

Even if surface syntax remains minimal, the TS kernel should expose a uniform internal interface with
**both** stable-head primitives:

- a stable head for functor hom-action at a cell (surface-intended `F₁(f)`), and
- a stable head for transfor off-diagonal (surface-intended `ϵ_(f)`).

Then we relate the two *computationally* by either:

- a **unification rule** equating them (treating them as definitionally convertible), or
- a **rewrite rule** that orients one toward the other, e.g. `(1_F)_(f) ↪ F₁(f)` (or the opposite),
  depending on which head you want as canonical normal form.

This mirrors the emdash2 approach: keep stable heads explicit, and add small conversion/rewriting bridges
between equivalent presentations, so normalization is predictable.

---

## 6. Proposed TS kernel changes (conceptual, not code yet)

Starting point: `emdash1/src/types.ts` and the existing elaboration mechanism.

### 6.1. Add binder modes to core binders/context

Add a binder-mode field to:

- context `Binding` entries, and
- binder nodes (`Lam` / `Pi`), so the annotation survives discharge and can be consulted by `*_int_*`
  operations and their rewrite theory.

Additionally, record (explicitly or derivably) the controlling category of variation.

### 6.2. Introduce transfor intro/discharge operator(s)

Add a new core constructor (name TBD) analogous to `MkFunctorTerm`, which:

- takes `A B F G`,
- takes a diagonal family under a `:^nat` binder,
- produces a term of type `Transf F G`,
- and makes naturality computational via the `tapp1_int_*` elimination/rewrite story (not by asking the
  user for a separate naturality proof).

### 6.3. Introduce elimination stable heads for transfors

Add stable heads corresponding to emdash2’s projection/apply interface:

- diagonal projection (`tapp0`-like),
- off-diagonal projection (`tapp1`-like), and potentially packaged-as-functor variants (ω-friendly).

Their computation rules should be rewrite rules that trigger on stable heads introduced by the new
discharge operators.

### 6.4. Align functor arrow-action with transfor off-diagonal

Provide an internal derived operator:

- `F₁(f) := (1_F)_(f)`

either as a definitional rewrite or as a derived macro at the TS level.

---

## 7. Practical roadmap (functors-only first, then transfors)

1) **Kernel binder modes**: implement mode annotations in `types.ts` and context handling.
2) **Functor packaging and ω-friendly hom-action**:
   - keep `MkFunctorTerm` as the canonical introduction,
   - add an explicit “packaged hom-action” head if needed (emdash2-style split between functor-level action
     and capped application).
3) **Transfor introduction (`:^nat` discharge)**:
   - implement transfor intro operator + diagonal projection,
   - implement the internal `tapp1_int_*`-style packaging that forces the off-diagonal binder discipline
     (`f :^func (Hom_cat A x y)`).
4) **Accumulation rewrite laws**:
   - add the “cut accumulation” rewrite rules on off-diagonal stable heads to normalize pasting/exchange.
5) **Extend to displayed categories and `homd_int`** once the binder discipline and discharge operators
   are validated on the base functor/transfor fragment.

---

## 8. Summary of the agreed core design principles

1) Don’t add special variable nodes (`CVar`, `FVar`); keep `Var` simple.
2) Do add **mode-annotated binders/context entries** (and track controlling categories).
3) Treat emdash2 `*_int_*` symbols as **explicit named discharge/abstraction operators** with rewrite theory.
4) Keep `:^func` as a **standalone** binder mode for functorial variation (independent of `:^nat`).
5) Under the intended meaning of `:^nat`, introducing a `Transf` needs only diagonal data;
   off-diagonal is derived by eliminators (`tapp1_int_*`) and computes by rewrite.
6) Off-diagonal binder `f` is `:^func` because it is an argument to a functor whose domain is a hom-category
   (`Hom_cat A x y`), not because of accumulation.
7) For uniformity, keep **both** primitives `F₁(f)` and `ϵ_(f)`, and relate them computationally at
   identity transfors (e.g. by a unification rule `F₁(f) ≡ (1_F)_(f)` or an oriented rewrite such as
   `(1_F)_(f) ↪ F₁(f)`), choosing a canonical head for normal forms.
