/*
  m— / emdash2                                                                 // project name (“m—” / “emdash”), version 2
  Functorial programming for (strict/lax) ω-categories in Lambdapi.             // overall intent: ω-categories, ω-functors, ω-transformations

  Design note: this file is intentionally “kernel-like”.                        // we keep primitives small and rewrite/unif rules explicit
  Comments aim to align names with standard category-theory terms.              // helps IDE autocompletion and cross-referencing textbooks/wikis
*/                                                                              // end header

flag "eta_equality" on;                                                         // enable η-reduction in definitional equality (normalization)

/*
  Rewriting hygiene (important for performance and robustness)

  Lambdapi rewrite rules are matched modulo conversion and are typechecked for subject reduction.
  A common pitfall is to over-specify inferred/implicit arguments on the LHS of a rule, especially
  when they are “complex” terms rather than pattern variables.

  Rule of thumb:
  - In the LHS, keep inferred arguments as `_` unless they are essential discriminators.
    Even if you “know” what an implicit argument should be, forcing it can trigger expensive
    conversion/unification work (or timeouts) when Lambdapi tries to prove it definitionally equal
    to the inferred one.

  - Often there are *multiple* such inferred arguments in nested applications (e.g. multiple `fapp0`s).
    Omitting only one may not be enough: any remaining explicit “complex” implicit argument can still
    force costly conversions.

  - Be extra cautious when an implicit argument contains a “cut” (a reducible subterm), e.g. an
    expression like `Hom_cat W (fapp0 F X)` on the LHS: since `fapp0 F X` may itself reduce, spelling
    out the whole implicit argument can make matching/typechecking much harder than using `_`.

  - Prefer small-step computation rules with stable heads (introduce a helper symbol when useful),
    rather than a single giant nested redex.

  We use these principles repeatedly below (e.g. for `hom_cov` computation rules).
*/

/*
  Naming conventions (emdash2.lp)

  Goal: keep “what lives where?” obvious at a glance, while preserving the standard CT habit that
  lowercase letters are morphisms/cells and uppercase letters are objects/structures.

  - Categories (terms of `Cat`): uppercase `A B C ...` (and `Z` often as a “base” category).
  - Objects of a category `A` (terms of `τ (Obj A)`): uppercase with suffix `_A`, e.g. `X_A, Y_A, W_A`.
  - 1-cells / arrows (objects of a hom-category): lowercase `f g h`, often with endpoint hint `f_XY`.
    In code: `f : τ (Obj (Hom_cat X_A Y_A))`.
  - Functors (objects of `Functor_cat A B`): uppercase `F G`, optionally `F_AB` when ambiguity helps.
  - Displayed/(iso)fibrations over a base `B` (terms of `Catd B`): use “total-space” letters `E D M ...`,
    e.g. `E : Catd B`. Avoid `A : Catd B` to prevent confusion with base categories.
  - Fibre objects (objects of `Fibre_cat E X_B`): uppercase like `U_EX` (read: U in E over X).
  - Displayed functors in the slice (objects of `Functord_cat E D` over the same base): use `FF GG ...`.
  - 2-cells/transformations: Greek `ϵ η ...`; 3-cells/modifications: `α μ ν ...` (when used).

  Symbol naming (computational interface)

  We try to name “application/projection” operations schematically, to make iteration predictable:

  - `fapp0` / `fapp1_func`:
      object-action / hom-action of an *ordinary* functor object `F : Obj(Functor_cat A B)`.
  - `fdapp0` / `fdapp1_funcd`:
      object-action / hom-action of a *displayed* functor object `FF : Obj(Functord_cat E D)`.
      (The `...funcd` suffix indicates “packaged as a displayed functor”.)
  - `tapp*` / `tdapp*`:
      analogous “application/projection” operations for transfors and displayed transfors.

  When we introduce a “packaged as functor” symbol like `tapp1_func_funcd` or `tdapp1_func_funcd`, we generally also
  introduce its components `*_fapp0_*` and `*_fapp1_*`, and add β-rules of the form
    `fapp0 ( ..._func ... ) ↪ ..._fapp0_...`   and   `fapp1_func ( ..._func ... ) ↪ ..._fapp1_...`.
  This keeps rewriting stable (head symbols are explicit) and avoids relying on unfolding definitional abbreviations.
*/

// -------------------------------------------------------------------------------------------------
// 0. Universes / “underlying ∞-groupoids” (sets-as-groupoids)                                     // foundational layer
// -------------------------------------------------------------------------------------------------

// `TYPE` is Lambdapi's meta-universe of collections.                                               // meta-level “type of types”
// In the object-language (emdash), any `ABC : TYPE` is a collection/classifier.                    // object-language classifiers
constant symbol Grpd : TYPE;                                                                        // classifier of “∞-groupoids” (think: types/sets)
injective symbol τ : Grpd → TYPE;                                                                   // decoding: underlying Lambdapi type of elements
builtin "T" ≔ τ;                                                                                   // Lambdapi builtin: interpret object-language types
builtin "Prop" ≔ Grpd;                                                                             // Lambdapi builtin: propositions live in `Grpd` here
builtin "P" ≔ τ;                                                                                   // Lambdapi builtin: interpretation of propositions-as-types

// -------------------------------------------------------------------------------------------------
// 1. Equality / path groupoid (id-type valued in `Grpd`)                                           // HoTT-style equality
// -------------------------------------------------------------------------------------------------

// Equality is valued in `Grpd` (not a separate `Prop`), i.e. “paths form a groupoid”.              // equality as ∞-groupoid
constant symbol = : Π [a: Grpd], τ a → τ a → Grpd;                                                  // identity type: x = y : Grpd
notation = infix 10;                                                                               // infix notation for `=`

// Reflexivity (identity path).                                                                      // refl
constant symbol eq_refl : Π [a: Grpd], Π x: τ a, τ (x = x);                                         // eq_refl x : x = x

// Path induction / J eliminator (dependent elimination for equality).                               // eqind / ind_eq
symbol ind_eq : Π [a: Grpd], Π [x: τ a], Π [y: τ a],                                                // parameters: type a and endpoints x,y
  τ (x = y) → Π p: (τ a → Grpd), τ (p y) → τ (p x);                                                  // eliminate equality into a family p
rule ind_eq (eq_refl $x) $p $u ↪ $u;                                                               // computation rule: J refl reduces

// Hook equality primitives into Lambdapi's standard names.                                          // interop with tactics/notations
builtin "eq"    ≔ =;                                                                               // builtin equality symbol
builtin "refl"  ≔ eq_refl;                                                                         // builtin reflexivity proof
builtin "eqind" ≔ ind_eq;                                                                          // builtin equality induction

// -------------------------------------------------------------------------------------------------
// 2. Tiny inhabited type (for “always-true” unif_rule side conditions)                              // unification hack
// -------------------------------------------------------------------------------------------------

// Pattern: `unif_rule ... ↪ [ tt ≡ tt ]` gives an unconditional unification hint.                   // used in cartierSolution13.lp
inductive unit : TYPE ≔ | tt : unit;                                                               // unit type with sole inhabitant

// Universe code for the unit type (so we can make `Obj Terminal_cat` compute definitionally).       // unit as a Grpd-code
constant symbol Unit_grpd : Grpd;
rule τ Unit_grpd ↪ unit;

// -------------------------------------------------------------------------------------------------
// 3. Natural numbers (used as a dimension/index type in drafts)                                     // globular/simplicial indices
// -------------------------------------------------------------------------------------------------

inductive nat : TYPE ≔                                                                              // Peano naturals as an index object
| zero : nat                                                                                           // zero (dimension 0)
| succ : nat → nat;                                                                                    // successor (dimension n+1)

// -------------------------------------------------------------------------------------------------
// 4. Categories as a classifier `Cat : TYPE` with `Obj : Cat → Grpd` and `Hom_cat : ... → Cat`          // strict ω-category skeleton
// -------------------------------------------------------------------------------------------------

constant symbol Cat : TYPE;                                                                         // classifier of (strict/lax) ω-categories

// Objects of a category form a groupoid (`Grpd`), not just a set.                                   // higher-categorical “objects up to paths”
//
// IMPORTANT (design): `Obj` is intentionally *not* injective in this development.
// Reason: we want definitional equalities like `Obj (Op_cat A) ↪ Obj A` (and `τ` is injective),
// so making `Obj` injective would collapse `Op_cat A ≡ A` by conversion, which is not intended.
symbol Obj : Cat → Grpd;                                                                            // object classifier of a category

// Hom_cat is itself a category: for X,Y : Obj(A), Hom_A(X,Y) : Cat.                                     // hom-categories (enriched/globular view)
injective symbol Hom_cat : Π [A : Cat] (X_A Y_A : τ (Obj A)), Cat;                            // hom-category as a Cat

// Identity morphism: an object in the hom-category Hom_A(X,X).                                      // identity 1-cell (and higher units implicitly)
injective symbol id : Π (A : Cat), Π (X_A: τ (Obj A)), τ (Obj (@Hom_cat A X_A X_A));        // id_X : Obj(Hom_cat_A(X,X))

// -------------------------------------------------------------------------------------------------
// 4b. Opposite category (core)                                                                      // A ↦ Aᵒᵖ (objects fixed, arrows reversed)
// -------------------------------------------------------------------------------------------------

injective symbol Op_cat : Cat → Cat;                                                                 // opposite category operation
rule Op_cat (Op_cat $A) ↪ $A;                                                                        // involutive law: (Aᵒᵖ)ᵒᵖ ≡ A

// Objects are unchanged by opposite.                                                                // Obj(Aᵒᵖ) ≡ Obj(A)
rule Obj (Op_cat $A) ↪ Obj $A;

// Homs are reversed by opposite.                                                                    // Hom_{Aᵒᵖ}(X,Y) ≡ Hom_A(Y,X)
rule @Hom_cat (Op_cat $A) $X $Y ↪ @Hom_cat $A $Y $X;

// Forward declaration: terminal category (used by displayed-category rules below).                   // 1 : Cat
constant symbol Terminal_cat : Cat;

/*
  OBSERVATION (cartierSolution13.lp vs emdash.lp, and why emdash2 keep *both* forms):

  - In cartierSolution13.lp, many core constructions are "objects in functor categories", i.e. functors
    `A → B` (and then transformations between them). This is the "parametric/object-in-context" view:
      F : Obj(Functor_cat(A,B))  behaves like "an object of B in the context A".

  - In emdash.lp (1-category draft), one often works directly with "pointwise" data:
      a : Hom_cat(X,Y)   (a single 1-cell, 0-dimensional as data),
    and then adds rewrite/unification rules so computation is easy.

  - In emdash2 (ω-categories), `Hom_A(X,Y)` is itself a category, so a "morphism" X→Y is
    an *object* of that hom-category: `Obj(Hom_A(X,Y))`. Higher morphisms live in the hom-category too.

  This creates a useful tension:
  (1) the *internal/semantic* composition is best packaged as a *functor*
        ∘ : Hom_cat(Y,Z) × Hom_cat(X,Y) → Hom_cat(X,Z)
      i.e. an object of `Functor_cat(Product_cat(Hom_cat Y Z)(Hom_cat X Y)) (Hom_cat X Z)`.
      This is faithful to the ω-story: functoriality (and hence higher coherence) is "baked in" by typing.

  (2) the *computational/pointwise* composition is the "application at objects" of that functor:
        comp_fapp0 g f : Obj(Hom_cat(X,Z)).
      This is the handle on which we can hang rewrite/unification rules (as we did in emdash.lp).

  Below, `comp_fapp0` is the pointwise operation, and `comp_func` is the functorial packaging.
  The rewrite rule later ("β-rule for composition functor") connects them.
*/

// Composition at object-level in a hom-category: (g : Hom_cat(Y,Z)) and (f : Hom_cat(X,Y)) compose to Hom_cat(X,Z). // pointwise / computational
symbol comp_fapp0 : Π [A : Cat], Π [X_A Y_A : τ (Obj A)], Π [Z_A: τ (Obj A)], // ambient A and objects
  Π (g: τ (Obj (@Hom_cat A Y_A Z_A))), Π (f: τ (Obj (@Hom_cat A X_A Y_A))),                                // composable morphisms g ∘ f
  τ (Obj (@Hom_cat A X_A Z_A));                                                                           // composite morphism in Hom_cat_A(X,Z)

// id and composition in the opposite category compute by forgetting the `Op_cat` wrapper.             // (Aᵒᵖ) has same identities, reversed composition
rule @id (Op_cat $A) $X ↪ @id $A $X;

// If g : Hom_{Aᵒᵖ}(Y,Z) and f : Hom_{Aᵒᵖ}(X,Y), then g∘f in Aᵒᵖ is f∘g in A.                             // reverse order
rule @comp_fapp0 (Op_cat $A) $X $Y $Z $g $f ↪ @comp_fapp0 $A $Z $Y $X $f $g;

// Sanity: identities/composition of Aᵒᵖ compute to those of A (with reversed order).                   // unit tests for the rewrite rules above
assert (A : Cat) (X : τ (Obj A)) ⊢ @id (Op_cat A) X ≡ @id A X;
assert (A : Cat) (X Y Z : τ (Obj A))
  (g : τ (Obj (@Hom_cat (Op_cat A) Y Z))) (f : τ (Obj (@Hom_cat (Op_cat A) X Y))) ⊢
  @comp_fapp0 (Op_cat A) X Y Z g f ≡ @comp_fapp0 A Z Y X f g;

/*
  MAINTENANCE INVENTORY (emdash2.lp)

  Goal: for each *Cat-valued construction* C (e.g. `Product_cat A B`), decide which core projections
  should compute definitionally (via rewrite rules), versus which should remain abstract / inferred
  (via `unif_rule`s or explicit lemmas).

  Core projections we care about for any `C : Cat`:
    - `Obj C                 : Grpd`                (and often a decoding rule for `τ (Obj C)`),
    - `Hom_cat C X Y         : Cat`,
    - `id C X                : Obj(Hom_cat C X X)`,
    - `comp_fapp0 C g f      : Obj(Hom_cat C X Z)` (pointwise composition),
    - `Op_cat C              : Cat`                (when relevant).

  Legend (current state in this file):
    - [OK]   there is a rewrite rule giving definitional computation
    - [INF]  no rewrite, but there is a unification rule that *infers* the intended constructor
    - [TODO] no rewrite/unif rule yet; behavior is currently abstract/unspecified
    - [HARD] needs new infrastructure (typically “universe objects” like `U : Grpd` with `τ U ↪ Grpd`)

  (A) Core / generic
    - `Cat`, `Obj`, `Hom_cat`, `id`, `comp_fapp0`: primitives of the kernel.

  (B) `Op_cat A` (opposite category)
    - `Obj (Op_cat A)`: [OK] `Obj (Op_cat A) ↪ Obj A`.
    - `Hom_cat (Op_cat A) X Y`: [OK] `Hom_cat (Op_cat A) X Y ↪ Hom_cat A Y X`.
    - `id (Op_cat A) X`: [OK] `id (Op_cat A) X ↪ id A X`.
    - `comp_fapp0 (Op_cat A) g f`: [OK] “reverse order” computation:
        if `g : Hom_{Aᵒᵖ}(Y,Z)` and `f : Hom_{Aᵒᵖ}(X,Y)`, then
        `comp_fapp0 (Op_cat A) X Y Z g f` should compute to `comp_fapp0 A Z Y X f g`.

  (C) `Terminal_cat`
    - `Obj Terminal_cat`: [OK] `Obj Terminal_cat ↪ Unit_grpd` with `τ Unit_grpd ↪ unit`.
      (Then `Terminal_obj : τ (Obj Terminal_cat)` lives in `unit`. We keep `Terminal_obj` as a stable
       constant head (no `Terminal_obj ↪ tt` rule yet) to avoid collapsing normal forms to `tt`.)
    - `Hom_cat Terminal_cat _ _`: [OK] `Hom_cat Terminal_cat _ _ ↪ Terminal_cat`.
    - `id Terminal_cat _`: [OK] `id Terminal_cat _ ↪ Terminal_obj`.
    - `comp_fapp0 Terminal_cat _ _ _ _ _`: [OK] `comp_fapp0 Terminal_cat ... ↪ Terminal_obj`.
    - (baseline note) In `cartierSolution13.lp`, there are also special-case computation rules like
      `Terminal_func Terminal_cat ↪ id_func`. In emdash2, this is still [TODO] (and depends on how we
      decide to represent `Obj Terminal_cat`).

  (D) `Product_cat A1 A2`
    - `Obj (Product_cat A1 A2)`: [OK] Σ-pairs (`Obj(A1×A2) ↪ Σ Obj(A1), Obj(A2)`).
    - `Hom_cat (Product_cat A1 A2) P Q`: [OK] pointwise product of hom-categories.
    - `id (Product_cat A1 A2) X`: [OK] computed componentwise.
    - `comp_fapp0 (Product_cat A1 A2) g f`: [OK] computed componentwise.
    - `Op_cat (Product_cat A1 A2)`: [OK] distributes pointwise.
    - (baseline note) In `cartierSolution13.lp`, there are also definitional “unit laws” like
      `Product_cat Terminal_cat A ↪ A` and `Product_cat A Terminal_cat ↪ A`. In emdash2, adding such
      definitional equalities likely requires first making `Obj Terminal_cat` compute (so that Σ over
      the unit groupoid can reduce).

  (E) `Functor_cat A B` (functor category, objects = functors)
    - `Obj (Functor_cat A B)`: [OK/by-design] intentionally abstract: we do *not* aim for a general
      computation rule exposing “functor data” as a Σ/record in emdash2 (so there is no global
      `τ (Obj (Functor_cat A B)) ↪ ...` rule).
    - `Hom_cat (Functor_cat A B) F G`: [OK] definitional identification with `Transf_cat F G`.
    - `id/comp_fapp0` inside `Functor_cat A B`: [PARTIAL] should be the usual “vertical” identity/composition
      of transfors. We currently do *not* expose these by definitional rules on `id` / `comp_fapp0` directly.
      Instead, the operational interface is via projections/packagings:
        • (id-instantiation at the “superscripted component” level): [OK]
            `tapp1_fapp0_funcd ... (id (Functor_cat A B) F)` folds to `fapp1_funcd ...` (stable head).
        • (pointwise 1-cell components of transfors): [OK]
            extracted by `tapp0_fapp0` (ordinary) and `tdapp0_fapp0` (displayed).
          In particular, the vertical id/composition *of components* is definitional via rewrite rules:
            (1_F)_Y ↪ id_{F(Y)}  and  (η∘ϵ)_Y ↪ η_Y ∘ ϵ_Y,
          and similarly in the displayed case via `tdapp0_fapp0`.
        • (higher components / modifications)
            a modification α : Hom_{Transf_cat(F,G)}(ϵ,ϵ') is *repackaged* by `tapp1_fapp1_func`
            (and `tdapp1_fapp1_func`) as a displayed transformation in `Transfd_cat`,
            whose pointwise components are then extracted by `tdapp0_fapp0`.

  (F) `Transf_cat F G` (transformations / transfors)
    - Main computational interface (what we *do* have):
        [OK] the projection/evaluation functors given by `tapp*` (and later `tapp0_fapp0`, `tapp1_*`)
        are the intended way to *use* a transfor without exposing its internal object encoding.
      In that sense, deciding `Obj(Transf_cat F G)` and `Hom_cat(Transf_cat F G) ϵ ϵ'` is not urgent
      unless we want definitional `id/comp_fapp0` in `Functor_cat A B` (since its homs reduce to transfors).
    - `Obj (Transf_cat F G)`: [OK/by-design] kept abstract for now (no Σ/record encoding).
    - `Hom_cat (Transf_cat F G) ϵ ϵ'`: [OK] will matter once we formalize modifications/3-cells explicitly.
    - `id/comp_fapp0` in `Transf_cat`: [OK] when we introduce these, we should simultaneously decide the
      computation behavior of the projection functors (`tapp*` / displayed `tdapp*`) on identities and
      composites, i.e. “components of (ϵ₂ ∘ ϵ₁) are (components of ϵ₂) ∘ (components of ϵ₁)”
      at the level of `tapp0_fapp0` / `tdapp0_fapp0` (and, for higher cells, via `tapp1_fapp1_func`
      landing in `Transfd_cat` + component extraction by `tdapp0_fapp0`).

  (G) Classifier categories `Grpd_cat` and `Cat_cat`
    - Intended: `τ (Obj Grpd_cat) ≡ Grpd` and `τ (Obj Cat_cat) ≡ Cat`.
    - Current mechanism: [OK] definitional computation via codes `Grpd_grpd` / `Cat_grpd` with
      `τ Grpd_grpd ↪ Grpd`, `τ Cat_grpd ↪ Cat`, and `Obj Grpd_cat ↪ Grpd_grpd`, `Obj Cat_cat ↪ Cat_grpd`.
    - `Obj Grpd_cat` / `Obj Cat_cat`: [OK] computes by rewriting.
    - `Hom_cat Grpd_cat X Y`: [OK] decoding computes to function types via `τ (Obj (Hom_cat ...)) ↪ (τ X → τ Y)`.
    - `Hom_cat Cat_cat X Y`: [OK] computes to `Functor_cat X Y`.

  (H) Displayed-category layer (`Catd`) and related Cat constructions
    - `Fibre_cat (Fibration_cov_catd M) x`: [OK] computes to `fapp0 M x`.
    - `Pullback_catd (Fibration_cov_catd E) F`: [OK] computes to `Fibration_cov_catd (E ∘ F)` (via `comp_fapp0` in `Cat_cat`).
    - `Total_cat (Fibration_cov_catd M)`: [OK] object decoding `τ (Obj (Total_cat ...))` is Σ-shaped.
    - `Total_cat E` for general `E : Catd B`: [TODO] no definitional object/hom computation (kept semantic/primitive).
    - `Hom_cat (Total_cat (Fibration_cov_catd M)) (x,u) (y,v)`: [OK] reduces to an (opposite of a) Grothendieck
      total category via `Groth_hom_fam` (so object-level morphisms become Σ-pairs `(f,α)` definitionally).

  (I) `Fibre_cat E x` (as a Cat-valued construction)
    - For `E = Lift_catd A`: [OK] `Fibre_cat (Lift_catd A) _ ↪ A`.
    - For `E = Fibration_cov_catd M`: [OK] `Fibre_cat (Fibration_cov_catd M) x ↪ fapp0 M x`.
    - In general: [TODO/by-design] `Catd B` is already intended to classify *isofibrations* (not mere `Cat/B`),
      but we have not yet introduced the explicit “iso-transport / cleavage” operations witnessing that
      isofibration structure. Until that interface is added, we keep general `Catd` computations abstract
      and only add concrete rewrite rules for special constructors (`Terminal_catd`, `Fibration_cov_catd`, etc.).
*/

// -------------------------------------------------------------------------------------------------
// 5. Functors (as objects of a functor-category `Functor_cat A B : Cat`)                                // ω-functors
// -------------------------------------------------------------------------------------------------

// The “functor category” between A and B (objects are functors, morphisms are transformations).     // internal functor category
constant symbol Functor_cat : Π (A B : Cat), Cat;                                            // Functor_cat(A,B) : Cat

// Inference helper (since `Obj` is not injective): allow recovering the domain/codomain cats from an equality of functor-object classifiers. // replaces prior convenience
unif_rule Obj (Functor_cat $A $B) ≡ Obj (Functor_cat $A' $B') ↪ [ $A ≡ $A'; $B ≡ $B' ];

// Action of a functor on objects.                                                                   // F₀ : Obj(A) → Obj(B)
symbol fapp0 : Π [A B : Cat], Π (F_AB : τ (Obj (Functor_cat A B))),                            // functor object F ∈ Obj(Functor_cat(A,B))
  τ (Obj A) → τ (Obj B);                                                                            // send X_A ↦ F_AB(X_A)

// Action of a functor on hom-categories: gives a functor Hom_A(X,Y) → Hom_B(FX,FY).                 // F₁ as a functor (ω-level)
symbol fapp1_func : Π [A B : Cat], Π (F_AB : τ (Obj (Functor_cat A B))),                            // functor object F
  Π [X_A Y_A : τ (Obj A)],                                                            // endpoints
  τ (Obj (Functor_cat (@Hom_cat A X_A Y_A) (@Hom_cat B (fapp0 F_AB X_A) (fapp0 F_AB Y_A))));        // functor on the hom-category

// Opposite of a functor: F : A→B  ↦  Fᵒᵖ : Aᵒᵖ → Bᵒᵖ (same object-map, reversed hom-action).        // dualization of functors
injective symbol Op_func : Π [A B : Cat],
  τ (Obj (Functor_cat A B)) → τ (Obj (Functor_cat (Op_cat A) (Op_cat B)));

// Involution: (Fᵒᵖ)ᵒᵖ ≡ F (definitionally, up to Op_cat involution).                                 // (−)ᵒᵖ is involutive
rule Op_func (@Op_func $A $B $F) ↪ $F;

// Object-action is unchanged by opposite.                                                            // Fᵒᵖ₀ = F₀
rule @fapp0 _ _ (@Op_func $A $B $F) $xA ↪ @fapp0 $A $B $F $xA;

// Hom-action is reversed by opposite (uses definitional Hom_{Aᵒᵖ}(X,Y) ≡ Hom_A(Y,X)).                // Fᵒᵖ₁(X,Y) = F₁(Y,X)
rule @fapp1_func _ _ (@Op_func $A $B $F) $X $Y
  ↪ @fapp1_func $A $B $F $Y $X;

// -------------------------------------------------------------------------------------------------
// 6. Classifier categories: `Grpd_cat` and `Cat_cat` (categories of groupoids and categories)       // “universes as categories”
// -------------------------------------------------------------------------------------------------

// Universe codes for classifier objects (so τ(Obj Grpd_cat) and τ(Obj Cat_cat) compute).              // definitional computation for “objects are groupoids/categories”
// Design: we keep these as explicit codes in `Grpd` (like `Σ_`) rather than as special-cased τ-rules.  // extensible, uniform pattern
constant symbol Grpd_grpd : Grpd;                                                                     // code whose decoding is Grpd
constant symbol Cat_grpd  : Grpd;                                                                     // code whose decoding is Cat
rule τ Grpd_grpd ↪ Grpd;
rule τ Cat_grpd  ↪ Cat;

// `Grpd_cat` plays the role of the category of groupoids/sets (discrete fibrations classifier).     // analogue of Set/Type-as-a-category
constant symbol Grpd_cat : Cat;                                                                     // category of ∞-groupoids
rule Obj Grpd_cat ↪ Grpd_grpd;                                                                        // objects of Grpd_cat decode to Grpd
rule τ (Obj (@Hom_cat Grpd_cat $X $Y)) ↪ (τ $X → τ $Y);                                                  // morphisms in Grpd_cat are functions

// `Cat_cat` is the category of categories (fibrations classifier).                                  // Cat of categories
constant symbol Cat_cat : Cat;                                                                      // category of categories
rule Obj Cat_cat ↪ Cat_grpd;                                                                          // objects of Cat_cat decode to Cat
rule @Hom_cat Cat_cat $X $Y ↪ Functor_cat $X $Y;                                                            // morphisms in Cat_cat are functors

// Sanity: the intended decoding holds by definitional computation.                                   // τ(Obj Grpd_cat) ≡ Grpd, τ(Obj Cat_cat) ≡ Cat
assert ⊢ τ (Obj Grpd_cat) ≡ Grpd;
assert ⊢ τ (Obj Cat_cat) ≡ Cat;

// Opposites fix the classifier categories (definitionally).                                          // Grpdᵒᵖ ≡ Grpd, Catᵒᵖ ≡ Cat
rule Op_cat Grpd_cat ↪ Grpd_cat;
rule Op_cat Cat_cat ↪ Cat_cat;

// Internalized opposite as a functor in Cat: op : Cat_cat → Cat_cat.                                 // A ↦ Aᵒᵖ, F ↦ Fᵒᵖ
// This is the “usual” dualization, but packaged as an object of Functor_cat(Cat_cat,Cat_cat),
// so we can postcompose Cat-valued fibrations E : B → Cat_cat with `op`.
//
// Terminology / intent (“twisted fibration”):
//
// - A (pseudo)functor E : B → Cat corresponds (via Grothendieck construction / unstraightening) to a
//   Grothendieck *opfibration* p : ∫E → B.  Concretely:
//     • objects of ∫E are pairs (b, e) with b : Obj(B) and e : Obj(E(b));
//     • a morphism (b,e) → (b',e') lying over f : b→b' in B is (informally) a morphism
//           E(f)(e) → e'   in the fibre category E(b').
//
// - Postcomposing with opposite yields Eᵒᵖ : B → Cat, where Eᵒᵖ(b) ≔ (E(b))ᵒᵖ, still covariant in b,
//   hence still an opfibration.  But it “twists” the direction *inside fibres*:
//     a morphism over f : b→b' from (b,e) to (b',e') in ∫(Eᵒᵖ) is equivalently a morphism
//           e' → E(f)(e)   in E(b')           (since arrows in E(b')ᵒᵖ are reversed).
//
// This matches the intended reading: transport along base arrows stays covariant, while fibre arrows
// are read in the opposite direction (“target-to-transport(source)”).
constant symbol op : τ (Obj (Functor_cat Cat_cat Cat_cat));

// Object-action: op₀(A) ≡ Aᵒᵖ.                                                                       // fapp0(op,A) ↪ Op_cat(A)
rule @fapp0 _ _ op $A ↪ Op_cat $A;

// Morphism-action on objects (functors): op₁(F) ≡ Fᵒᵖ.                                               // fapp0(fapp1_func(op),F) ↪ Op_func(F)
rule @fapp0 (Functor_cat $A1 $A2) _
  (@fapp1_func Cat_cat Cat_cat op $A1 $A2) $F ↪ @Op_func $A1 $A2 $F;

// Identity functor on a category A (as an object in Functor_cat(A,A)).                                  // 1-category identity, lifted to ω setting
symbol id_func [A: Cat] : τ (Obj (Functor_cat A A))                                             // identity functor id_A : Obj(Functor_cat(A,A))
≔ @id Cat_cat A;                                                                        // defined as identity morphism in Cat_cat
// NOTE: `id_func` is currently a definitional abbreviation; if we ever need rewrite rules with head `id_func`, switch to `symbol id_func ...;` + `rule id_func ... ↪ ...` (cf. tapp0_fapp0).
rule fapp0 (@id Cat_cat $A) $xA ↪ $xA;                                                   // computation: (id_A)(x) ↪ x

// Composition of functors (as morphisms in Cat_cat) computes pointwise on objects.                     // (F∘G)(x) ↪ F(G(x))
rule @fapp0 $A $C (@comp_fapp0 Cat_cat $A $B $C $F $G) $x
  ↪ @fapp0 $B $C $F (@fapp0 $A $B $G $x);

// Opposite of identity is identity.                                                                  // (id_A)ᵒᵖ ≡ id_{Aᵒᵖ}
rule @Op_func _ _ (@id_func $A) ↪ @id_func (Op_cat $A);

// Opposite respects composition of functors (in Cat_cat).                                            // (F∘G)ᵒᵖ ≡ Fᵒᵖ∘Gᵒᵖ
rule @Op_func _ _ (@comp_fapp0 Cat_cat $A1 $A2 $A3 $F $G)
  ↪ @comp_fapp0 Cat_cat (Op_cat $A1) (Op_cat $A2) (Op_cat $A3) (@Op_func $A2 $A3 $F) (@Op_func $A1 $A2 $G);

// Covariant “hom functor” / Yoneda-style precomposition: Hom_A(W, F(-)).                             // hom-covariant / representable functor core
constant symbol hom_cov : Π [A : Cat], Π (W_A: τ (Obj A)), Π [B : Cat],                               // W_A ∈ Obj(A), F : Functor_cat(B,A)
  Π (F_BA : τ (Obj (Functor_cat B A))), τ (Obj (Functor_cat B Cat_cat));                                     // result: B → Cat_cat (a Cat-valued functor)
rule fapp0 (@hom_cov $A $W $B $F) $Y ↪ @Hom_cat $A $W (fapp0 $F $Y);                                     // object action: Y ↦ Hom_A(W, F(Y))

// Contravariant “hom functor”: Hom_A(F(-), W), packaged as a covariant functor on Bᵒᵖ.               // hom-contravariant / dual representable
// Usual notation: `Hom_A(F(-),W) : Bᵒᵖ → Cat` (or Set/Grpd in 1-categorical cases).                   // variance reminder
symbol hom_con : Π [A : Cat], Π (W_A: τ (Obj A)), Π [B : Cat],                                        // W_A ∈ Obj(A), F : Functor_cat(B,A)
  Π (F_BA : τ (Obj (Functor_cat B A))), τ (Obj (Functor_cat (Op_cat B) Cat_cat));                            // result: Bᵒᵖ → Cat_cat

// Definition: Hom_A(F(-),W) is the same as Hom_{Aᵒᵖ}(W,(Fᵒᵖ)(-)), pointwise.                           // implement hom_con via hom_cov + opposites
rule @hom_con $A $W $B $F ↪ @hom_cov (Op_cat $A) $W (Op_cat $B) (@Op_func $B $A $F);

/*
  Computation (hom_cov acts by postcomposition):

    ((Hom_A(W,F-))_1 f)_0 g  ↪  (F f) ∘ g.

  Concretely:
    - f : Hom_B(X,Y)
    - g : Hom_A(W,F(X))
  then hom_cov(W,F) : B → Cat induces the functor
    Hom_A(W,F(X)) → Hom_A(W,F(Y))
  sending g ↦ (F f) ∘ g.

  Performance note:
  We intentionally keep some category arguments on the LHS as `_` to avoid expensive conversions
  and brittle matching on reducible subterms (especially when implicit arguments would contain things
  like `fapp0 $F $X` or `Op_cat _`).
*/

rule @fapp0 (@Hom_cat $A $W _)
    (@Hom_cat $A $W _)
    (@fapp0 (@Hom_cat $B $X $Y)
      _
      (@fapp1_func $B Cat_cat (@hom_cov $A $W $B $F) $X $Y) $f) $g
  ↪ @comp_fapp0 $A $W (fapp0 $F $X) (fapp0 $F $Y)
      (@fapp0 (@Hom_cat $B $X $Y)
        (@Hom_cat $A (fapp0 $F $X) (fapp0 $F $Y))
        (@fapp1_func $B $A $F $X $Y) $f) $g;

// Postcomposition by op computes pointwise: (op ∘ E)(b) ≡ (E(b))ᵒᵖ.                                   // key for “twisted” fibrations
rule @fapp0 $B Cat_cat (@comp_fapp0 Cat_cat $B Cat_cat Cat_cat op $E) $b
  ↪ Op_cat (@fapp0 $B Cat_cat $E $b);

// Naturality w.r.t. precomposition in the argument functor: Hom_A(W, F(-)) ∘ G  ≡  Hom_A(W, (F∘G)(-)). // "accumulate the functor"
// Note: we express functor composition via `comp_fapp0` in `Cat_cat` (not via `comp_cat_fapp0`, which is defined later). // computational-friendly
rule @comp_fapp0 Cat_cat $C $B Cat_cat (@hom_cov $A $W $B $F) $G
  ↪ @hom_cov $A $W $C (@comp_fapp0 Cat_cat $C $B $A $F $G);

// Naturality w.r.t. precomposition in the argument functor (contravariant case):                    // accumulate the functor (with Op)
// Hom_A(F(-),W) ∘ (Gᵒᵖ)  ≡  Hom_A((F∘G)(-), W), where Gᵒᵖ : Cᵒᵖ → Bᵒᵖ.                                  // variance bookkeeping
rule @comp_fapp0 Cat_cat _ _ Cat_cat (@hom_con $A $W $B $F) (@Op_func $C $B $G)
  ↪ @hom_con $A $W $C (@comp_fapp0 Cat_cat $C $B $A $F $G);

// Sanity: the above rewrite fires definitionally (conversion).                                        // exercise the rule
assert [A B : Cat] [C : Cat] (W : τ (Obj A))
  (F : τ (Obj (Functor_cat B A))) (G : τ (Obj (Functor_cat C B))) ⊢
  @comp_fapp0 Cat_cat C B Cat_cat (@hom_cov A W B F) G
    ≡ @hom_cov A W C (@comp_fapp0 Cat_cat C B A F G);

assert [A B : Cat] [C : Cat] (W : τ (Obj A))
  (F : τ (Obj (Functor_cat B A))) (G : τ (Obj (Functor_cat C B))) ⊢
  @comp_fapp0 Cat_cat (Op_cat C) (Op_cat B) Cat_cat (@hom_con A W B F) (@Op_func C B G)
    ≡ @hom_con A W C (@comp_fapp0 Cat_cat C B A F G);

// Sanity: hom_con is definitional to hom_cov in the opposite category, pointwise.                     // Hom_{Aᵒᵖ}(W, Fᵒᵖ(-)) = Hom_A(F(-),W)
assert [A B : Cat] (W : τ (Obj A)) (F : τ (Obj (Functor_cat B A))) (x : τ (Obj (Op_cat B))) ⊢
  fapp0 (hom_con W F) x
    ≡ fapp0 (@hom_cov (Op_cat A) W (Op_cat B) (@Op_func B A F)) x;

// Sanity: postcomposition by op normalizes pointwise.                                                // exercise `op ∘ E` computation
assert [B : Cat] (E : τ (Obj (Functor_cat B Cat_cat))) (b : τ (Obj B)) ⊢
  @fapp0 B Cat_cat (@comp_fapp0 Cat_cat B Cat_cat Cat_cat op E) b
    ≡ Op_cat (@fapp0 B Cat_cat E b);

// Sanity: opposite distributes over functor composition in Cat_cat.                                  // (F∘G)ᵒᵖ = Fᵒᵖ∘Gᵒᵖ
assert [A B C : Cat] (F : τ (Obj (Functor_cat B C))) (G : τ (Obj (Functor_cat A B))) ⊢
  @Op_func A C (@comp_fapp0 Cat_cat A B C F G)
    ≡ @comp_fapp0 Cat_cat (Op_cat A) (Op_cat B) (Op_cat C) (@Op_func B C F) (@Op_func A B G);

// Sanity: general hom_cov action computes to postcomposition.                                          // ((hom_cov W F)_1 f)_0 g ↪ (Ff)∘g
assert [A B : Cat] (W : τ (Obj A)) (F : τ (Obj (Functor_cat B A)))
  (X Y : τ (Obj B)) (f : τ (Obj (@Hom_cat B X Y))) (g : τ (Obj (@Hom_cat A W (fapp0 F X)))) ⊢
  @fapp0 (@Hom_cat A W (fapp0 F X))
    (@Hom_cat A W (fapp0 F Y))
    (@fapp0 (@Hom_cat B X Y)
      _
      (@fapp1_func B Cat_cat (@hom_cov A W B F) X Y) f) g
    ≡ @comp_fapp0 A W (fapp0 F X) (fapp0 F Y)
        (@fapp0 (@Hom_cat B X Y)
          (@Hom_cat A (fapp0 F X) (fapp0 F Y))
          (@fapp1_func B A F X Y) f) g;

// Internalized (bifunctorial) covariant hom: for fixed F:B→A, we get a functor Aᵒᵖ → (B → Cat).    // Hom_A(-,F(-)) as a functor
// In ordinary notation: hom_cov_int(F) : A^op ⇒ Functor_cat(B,Cat_cat), i.e. A^op ⇒ B ⇒ Cat.
constant symbol hom_cov_int : Π [A : Cat], Π [B : Cat],
  Π (F_BA : τ (Obj (Functor_cat B A))), τ (Obj (Functor_cat (Op_cat A) (Functor_cat B Cat_cat)));

// β-rule for object-action: at X : Obj(Aᵒᵖ) (i.e. X : Obj(A)), hom_cov_int(F)(X) ≡ hom_cov(X,F).   // fapp0(hom_cov_int(F),X) ↪ hom_cov(X,F)
rule fapp0 (@hom_cov_int $A $B $F) $X ↪ @hom_cov $A $X $B $F;

// Sanity: the β-rule fires, and the resulting functor still computes pointwise via hom_cov.         // exercise both rewrites
assert [A B : Cat] (F : τ (Obj (Functor_cat B A))) (X : τ (Obj (Op_cat A))) ⊢
  fapp0 (hom_cov_int F) X ≡ @hom_cov A X B F;

assert [A B : Cat] (F : τ (Obj (Functor_cat B A))) (X : τ (Obj (Op_cat A))) (Y : τ (Obj B)) ⊢
  fapp0 (fapp0 (hom_cov_int F) X) Y ≡ @Hom_cat A X (fapp0 F Y);


// -------------------------------------------------------------------------------------------------
// 7. Dependent categories (displayed categories over a base)                                        // Cat-valued type families
// -------------------------------------------------------------------------------------------------

// `Catd B` is the type of (mere) isofibrations over `B` (a.k.a. displayed categories with iso-lifts). // isofibration objects over B
// Concretely, an element `E : Catd B` should be thought of as a functor `p : Total_cat(E) ⟶ B`        // p : E → B
// together with an implicit/axiomatized “iso-lifting” interface (to be made explicit later).          // iso-lifts interface (future)
// It is therefore sound to *talk about* Cat/B intuition in comments, but the intended subtype is:     // Catd ⊆ Cat/B
//   Catd B  ⊆  Cat/B   (objects in the slice whose projection is an isofibration).
constant symbol Catd : Π (A : Cat), TYPE;                                                           // classifier of dependent categories over A

/*
  Visualization: (iso)fibrations as “simplicial” shapes (edges / surfaces / volumes / …)

  A helpful mental model in this development is to think of a (covariant) (iso)fibration `E → B` as
  a classifier of “arrows in B”, i.e. *edges*.

  Prototypical example (representable / co-slice codomain fibration):
  - Given `X_B : Obj(B)`, the representable functor `Hom_B(X_B,-)` is (in our notations) `hom_cov X_B`,
    or explicitly `hom_cov X_B (@id_func B) : Obj(Functor_cat B Cat_cat)`.
  - Its Grothendieck construction `Fibration_cov_catd (hom_cov X_B (@id_func B)) : Catd B`
    has fibre at `Y_B : Obj(B)` equal to `Hom_B(X_B,Y_B)` (by the rewrite rule for `Fibre_cat`).
    So an “element” over `Y_B` can be visualized as an arrow `X_B → Y_B` (an *edge*).

  Iteration suggests higher simplices:
  - A fibration `S → E` (i.e. a displayed category over `Total_cat E`) can be visualized as classifying
    “2-arrows”, i.e. *surfaces*. In our notations this is approximated by `homd_cov`.
    Notice in the type of `homd_cov` the base product
      `Product_catd B (Fibration_cov_catd (hom_cov W_Z (@id_func Z)))`,
    which formalizes that a “surface” is fibred over (at least) two “edges”: the usual codomain edge,
    plus an extra base edge coming from the fact that `E` itself already lies over `B`.
    This matches the 2-simplex picture in `dependent-category-2-simplex.png`.

  - A further fibration `V → S` would similarly classify “3-arrows”, i.e. *volumes*, now fibred over
    (recursively) several surface-like faces, matching `dependent-category-3-simplex.png`.

  This is one way the “simplicial” aspects of ω-categories emerge from iterating dependent categories
  and Grothendieck constructions.
*/

// Terminal dependent category over A (constant fibration with terminal fibres).                     // unit family / trivial fibration
constant symbol Terminal_catd : Π (A : Cat), Catd A;                                                 // terminal displayed category

// Grothendieck construction: a Cat-valued functor A → Cat_cat gives a Grothendieck-style display over A. // category of elements / ∫ construction
// Terminology note: a covariant functor A → Cat typically corresponds to an *opfibration* ∫E → A.    // naming vs semantics
// We keep the historical name `Fibration_cov_catd` for now; we can rename once the (op)fibration interface is stabilized.
constant symbol Fibration_cov_catd : Π [A : Cat], τ (Obj (Functor_cat A Cat_cat)) → Catd A;               // ∫M : Catd(A) for M : A → Cat

/*
  Displayed/dependent functors: slice-style vs general base functor

  - In cartierSolution13.lp, a displayed functor can be "over an arbitrary base functor":
      funcd A F B   (A : catd X, B : catd Y, F : func X Y)
    so a displayed morphism remembers a base map F : X → Y.
    Composition then produces a displayed functor over the composite base map (F∘G).

	  - In emdash2.lp we choose the *slice-style* presentation (within isofibrations over a fixed base):
	      Functord_cat(F,E) where both displayed categories live over the same base B : Cat.
	    Concretely, this corresponds to working in a slice Cat/B (or the fibration over B):
	      objects: Catd B
	      morphisms: displayed functors over id_B (sections / maps over the identity).
    This has a pragmatic benefit: composition stays over the identity automatically, so we get a plain
    category of displayed functors with easy closure under composition.

  - We can still *simulate* “displayed over an arbitrary base functor” using pullback:
      given B : Catd(Y) and F : X → Y, first form the reindexed family F^*B : Catd(X),
      then a displayed functor over F becomes an ordinary slice-style displayed functor
      (over id_X) into the pullback:
        funcd_over(F) : A → B     ~    (A → Pullback_catd B F).
    For isofibrations coming from Grothendieck constructions, the rule below expresses exactly this:
      Pullback_catd (Fibration_cov_catd E) F  ↪  Fibration_cov_catd (E ∘ F).
*/

// `Functord_cat E D` is the category of functors over a fixed base `B` (in the isofibration slice).    // Fun_B(E,D) / hom in Cat/B
// Usual notation: if `p:E⟶B` and `q:D⟶B`, then an object of `Functord_cat(E,D)` is a functor `F:E⟶D`
// such that `q ∘ F = p` (i.e. a morphism in the slice category `Cat/B`).                               // commuting triangle
constant symbol Functord_cat : Π [B : Cat], Π (E D : Catd B), Cat;                          // Functord_cat(E,D) : Cat

// Inference helper (since `Obj` is not injective): allow recovering the base and displayed cats from an equality of displayed-functor classifiers. // replaces prior convenience
unif_rule Obj (@Functord_cat $B $E $D) ≡ Obj (@Functord_cat $B' $E' $D') ↪ [ $B ≡ $B'; $E ≡ $E'; $D ≡ $D' ];

// Dependent identity functor (identity section).                                                    // id in the slice category
constant symbol id_funcd [B : Cat] [E:Catd B] : τ (Obj (Functord_cat E E));                      // id : Obj(Functord_cat(E,E))

// Dependent composition of dependent functors.                                                      // composition in the slice Cat/B
symbol comp_catd_fapp0 [B : Cat] [E D : Catd B] [C:Catd B]                                   // base B and displayed categories E,D,C
  (FF: τ (Obj (Functord_cat D C))) (GG: τ (Obj (Functord_cat E D))) : τ (Obj (Functord_cat E C));               // compose : (D→C) × (E→D) → (E→C)

// Fibre of a dependent category E over X_B : Obj(B) (displayed category at a base object).          // E[X_B] in type theory
injective symbol Fibre_cat : Π [B : Cat] (E : Catd B) (X_B : τ (Obj B)), Cat;                          // fibre category at X_B

// Fibre of a Grothendieck construction is the original value (strictly, on objects).                // ∫M fibre at x is M(x)
rule Fibre_cat (Fibration_cov_catd $M) $x ↪ fapp0 $M $x;                                              // fibre(∫M,x) ↪ M(x)

// Fibre of the terminal displayed category is the terminal category.                                  // fibre(1_B, x) ≡ 1
// This is the displayed analogue of cartierSolution13's `Fibre_catd (Terminal_catd _) _ ↪ Terminal_catd _`. // terminal fibres
rule Fibre_cat (Terminal_catd $B) _ ↪ Terminal_cat;

// Sanity (derived instance): representable fibration.                                                 // fibre(∫Hom(X,F-),x) ≡ Hom(X,Fx)
// This is not an extra computation rule: it follows by rewriting with the general Grothendieck fibre
// rule above and the `hom_cov` object-action rule `fapp0 (hom_cov X F) x ↪ Hom_cat X (fapp0 F x)`.
assert [B A : Cat] (X_A : τ (Obj A)) (F : τ (Obj (Functor_cat B A))) (x : τ (Obj B)) ⊢
  Fibre_cat (Fibration_cov_catd (hom_cov X_A F)) x ≡ @Hom_cat A X_A (fapp0 F x);

// Pullback of a dependent category along a functor (reindexing/substitution).                       // substitution / base change
symbol Pullback_catd : Π [A B : Cat], Catd B → τ (Obj (Functor_cat A B)) → Catd A;               // F^*(E) : Catd(A)
rule Fibre_cat (Pullback_catd $E $F) $xA ↪ Fibre_cat $E (fapp0 $F $xA);                              // fibre(F^*E,x) ↪ fibre(E,Fx)

// Pullback along the identity functor is definitional identity.                                       // (id)^*(E) ≡ E
// NOTE: we pattern-match on `id Cat_cat A` (not on `id_func A`) because `id_func` is a definitional abbreviation. // stable matching
rule @Pullback_catd $A $A $E (@id Cat_cat $A) ↪ $E;

// Pullback of an isofibration (Grothendieck construction) is isofibration of the precomposition.    // ∫(E∘F) ≅ F^*(∫E)
// Here `E : B → Cat_cat` and `F : A → B`, and we express `E∘F` via composition in `Cat_cat`.         // avoids relying on later `comp_cat_fapp0`
// This is the key bridge for “general base functor” displayed maps: reindex first, then use Functord_cat. // simulate funcd-over-F
rule @Pullback_catd $A $B (@Fibration_cov_catd $B $E) $F
  ↪ @Fibration_cov_catd $A (@comp_fapp0 Cat_cat $A $B Cat_cat $E $F);

// -------------------------------------------------------------------------------------------------
// 7b. Opposite of displayed categories                                                             // (E→B) ↦ (Eᵒᵖ→Bᵒᵖ)
// -------------------------------------------------------------------------------------------------

injective symbol Op_catd : Π [X : Cat] (A : Catd X), Catd (Op_cat X);
rule Op_catd (Op_catd $A) ↪ $A;

// Opposite preserves terminal displayed categories.                                                  // (1_X)ᵒᵖ ≡ 1_{Xᵒᵖ}
rule @Op_catd _ (Terminal_catd $X) ↪ Terminal_catd (Op_cat $X);

// Opposite commutes with pullback (reindexing) via Op on the base functor.                            // (F^*E)ᵒᵖ ≡ (Fᵒᵖ)^*(Eᵒᵖ)
rule @Op_catd _ (@Pullback_catd $A $B $E $F)
  ↪ @Pullback_catd _ _ (@Op_catd $B $E) (@Op_func $A $B $F);

// -------------------------------------------------------------------------------------------------
// 8. Natural transformations (2-cells) as morphisms in functor categories                            // transfors
// -------------------------------------------------------------------------------------------------

// `Transf_cat(F,G)` is the category of natural transformations between F and G (and higher cells).      // 2-cells (and beyond)
constant symbol Transf_cat : Π [A B : Cat], Π (F G : τ (Obj (Functor_cat A B))), Cat; // Transf_cat(F,G) : Cat

/*
  tapp1_func_funcd (outer component / “superscript” viewpoint)

  Caution about notation: the binder `X : Obj(A)` here is an *external* projection index, not the usual
  “subscript object” of a natural transformation component.

  - Usual 1-categorical notation: for ϵ : Nat(F,G) and Y : Obj(A), we write ϵ_Y : Hom_cat(FY, GY).
    In our encoding, that *inner* index (Y) lives inside the representable `Hom_A(X,-)` and is not the
    explicit binder of `tapp1_func_funcd`.

  - Here `X` is better thought of as a superscript: ϵ ↦ ϵ^X, a map that takes a transformation ϵ and
    returns a dependent functor between representables:
      ϵ^X : Hom_A(X,-)  ⇒  Hom_B(FX, G(-)).
    The “subscript” can then be either:
      * an object Y (identity arrow), giving a component ϵ^X_Y,
      * or more generally an arrow f : Y₁ → Y₂, giving ϵ^X_f (naturality along f).

  - In the strict (non-lax) 1-categorical case, the familiar equation is:
      ϵ_{Y₂} ∘ F(f)  =  G(f) ∘ ϵ_{Y₁}.
    This is what “2-cell data” should satisfy; in the ω-setting it iterates inside hom-categories.

  Why package this as a functor (Transf_cat F G → Functord_cat(...))?
  - A modification α : ϵ ⇒ ϵ' (a 3-cell) has components expressed in terms of transformations, so after
    fixing the external index X, the source/target (ϵ, ϵ') become *functor-like* data (`tapp1_fapp0_funcd X ϵ`),
    letting us iterate: modifications → transformations between those component-functors → higher cells.
  - Extreme visualization: if A is Terminal_cat (only one X), then “projecting at X” is trivial and
    tapp becomes close to the idea that a natural transformation can be presented as a functorial object.

  Observation (common generalization; guided by types):

  `tapp1_func_funcd` is a “single ancestor” of:
  - `fapp1_funcd` (functorial action on homs, packaged as a displayed functor):
      specialize to the identity transfor ϵ := 1_F : Nat(F,F),
      then the packaged component (1_F)^X is definitionally `fapp1_funcd F [X]` (by the id-folding rule).

  - `tapp0_func` (ordinary pointwise component evaluation):
      specialize the external index to X := Y and then evaluate ϵ^Y at the identity arrow id_Y,
      yielding the usual component ϵ_Y : Hom_B(FY,GY), packaged as a functor in ϵ.

  So `tapp1_func_funcd` plays the role “project-to-a-functor between representables”, from which both
  “apply F to a 1-cell” and “extract the component ϵ_Y” arise as specializations.
*/
symbol tapp1_func_funcd : Π [A B : Cat], Π [F_AB G_AB : τ (Obj (Functor_cat A B))],                      // domain/codomain categories and functors
  Π (X_A: τ (Obj A)),                                                                                   // external/superscript projection index
  τ (Obj (Functor_cat (Transf_cat F_AB G_AB)
         (Functord_cat (Fibration_cov_catd (hom_cov X_A (@id_func A)))                             // source: Hom_A(X_A,-) over A
                  (Fibration_cov_catd (hom_cov (fapp0 F_AB X_A) G_AB)))));                               // target: Hom_B(FX_A, G_AB(-)) over A

// `tapp1_fapp0_funcd` is the fapp0 part of `tapp1_func_funcd`
symbol tapp1_fapp0_funcd : Π [A B : Cat], Π [F_AB G_AB : τ (Obj (Functor_cat A B))],                      // domain/codomain categories and functors
  Π (X_A: τ (Obj A)), Π (ϵ : τ (Obj (Transf_cat F_AB G_AB))),                                              // ϵ : Obj(Transf_cat(F,G))
  τ (Obj (Functord_cat (Fibration_cov_catd (hom_cov X_A (@id_func A)))                             // source: Hom_A(X_A,-)
                  (Fibration_cov_catd (hom_cov (fapp0 F_AB X_A) G_AB))));                                // target: Hom_B(FX_A, G_AB(-))

// β-rule: `tapp1_fapp0_funcd` is definitionally the object-action of the functor `tapp1_func_funcd`.               // unpack tapp1_func_funcd at objects
rule fapp0 (@tapp1_func_funcd $A $B $F_AB $G_AB $X_A) $ϵ ↪ @tapp1_fapp0_funcd $A $B $F_AB $G_AB $X_A $ϵ;

/*
  tapp0_func / tapp0_fapp0 (ordinary “component at Y”)

  In ordinary 1-category theory, a natural transformation ϵ : F ⇒ G has pointwise components
    ϵ_Y : Hom_B(FY, GY)
  (just a 1-cell in B).

  In this ω-development, we *derive* that 1-cell from the packaged/iterable viewpoint `tapp1_func_funcd`:
    - First specialize the external/superscript index to X := Y, giving ϵ^Y : Hom_A(Y,-) ⇒ Hom_B(FY,G(-)).
    - Then evaluate this dependent functor at the identity arrow id_Y : Hom_A(Y,Y).

  Important: `tapp0_fapp0` intentionally forgets the extra (lax) naturality *witnesses*.
  The laxness is carried by how ϵ^X acts on non-identity “2-arrow data” in the source representable,
  which in our framework is mediated by `homd_cov` (a displayed hom that is fibred over a product of
  a base edge and a displayed edge). Concretely, once `homd_cov` is implemented, ϵ^X will transport
  a non-identity 2-cell like “g : f ⇒ (g∘f)” to a non-identity 2-cell in the target encoding the
  lax naturality triangle (comparing something like (G g)∘(…) with (…) for the composite g∘f).

  The actual extracted “pointwise component” operation `tapp0_fapp0` is defined later in the file,
  after `fdapp0` is introduced (since it is implemented by evaluating `tapp1_fapp0_funcd` at the identity arrow).
*/

// Key identification: the hom-category of the functor-category is the transformation-category.      // Hom_{Functor_cat(A,B)}(F,G) ≅ Transf_cat(F,G)
rule @Hom_cat (Functor_cat _ _) $F $G ↪ Transf_cat $F $G;                                                        // definitional equality of homs


// -------------------------------------------------------------------------------------------------
// 9. Dependent sum / Σ-type (Grothendieck sum at the level of types)                                // Σ, projections
// -------------------------------------------------------------------------------------------------

// Dependent sum as an inductive “structure” type (σ : Σ x:a, P(x)).                                  // Σ-type as a record
inductive τΣ_ [a : Grpd] (P : τ a → Grpd) : TYPE ≔                                                   // τΣ_(P) is the decoded type of Σ_(P)
| Struct_sigma [a P] : Π (sigma_Fst : τ a) (sigma_Snd : τ (P sigma_Fst)), @τΣ_ a P;                  // constructor: (x, px)
notation τΣ_ quantifier;                                                                             // allow `τΣ_ x, ...` binder syntax

// `Σ_` is the code-level Σ-type (a classifier in `Grpd`); decoding maps it to `τΣ_`.                 // encoded Σ in the universe
constant symbol Σ_ [a : Grpd] (P : τ a → Grpd) : Grpd; notation Σ_ quantifier;                        // Σ_ P : Grpd
rule τ (Σ_ $P) ↪ τΣ_ $P;                                                                              // decoding computation rule: τ(Σ P) ↪ τΣ P

// First projection.                                                                                 // fst : Σ x, P x → a
injective symbol sigma_Fst [a P] (s : @τΣ_ a P) : τ a;                                                // σ₁ : τ(a)
rule sigma_Fst (Struct_sigma $1 $2) ↪ $1;                                                             // fst(x,px) ↪ x

// Second projection (dependent).                                                                     // snd : Σ x, P x → P(fst σ)
injective symbol sigma_Snd [a P] (s : @τΣ_ a P) : τ (P (sigma_Fst s));                               // σ₂ : τ(P(σ₁))
rule sigma_Snd (Struct_sigma $1 $2) ↪ $2;                                                             // snd(x,px) ↪ px

// -------------------------------------------------------------------------------------------------
// 10. Total category / comprehension (Grothendieck category of elements)                             // ∫ / context extension
// -------------------------------------------------------------------------------------------------

// `Total_cat(M)` is the total category (a.k.a. category of elements / comprehension).               // Σ at the level of categories
symbol Total_cat [B : Cat] (E: Catd B) : Cat;                                                        // ∫E : Cat

// Projection π₁ : Total_cat(M) → A (the “base” projection).                                          // comprehension projection
injective symbol Total_proj1_func [B : Cat] (E: Catd B) : τ (Obj (Functor_cat (Total_cat E) B));           // functor object in Functor_cat(∫E, B)

// Total of the opposite displayed category is the opposite of the total category.                    // ∫(Eᵒᵖ) ≡ (∫E)ᵒᵖ
// Orientation choice:
//   We normalize totals-of-opposites *outwards*, so that terms like `Total_cat (Op_catd E)` reduce to
//   `Op_cat (Total_cat E)`. This makes it easier to reuse the Grothendieck Σ-object rule for
//   `Total_cat (Fibration_cov_catd ...)` and then forget that `Op_cat` does not change objects.
//
// Matching note (important after dropping `injective Obj`):
//   We deliberately avoid patterns like `@Total_cat (Op_cat $B) (Op_catd $E)` on the LHS, because
//   `Op_cat _` is a *computing* subterm and syntactic matching may miss opportunities when the base is
//   only later inferred/normalized. Using `_` here relies on typing to force the base to be `Op_cat $B`.
rule @Total_cat _ (@Op_catd $B $E) ↪ Op_cat (@Total_cat $B $E);

// The projection of the opposite total is the opposite of the projection.                            // (π₁)ᵒᵖ ≡ π₁
rule @Op_func _ $B (@Total_proj1_func $B $E)
  ↪ @Total_proj1_func (Op_cat $B) (@Op_catd $B $E);

// -------------------------------------------------------------------------------------------------
// 10a. Grothendieck opfibration transport (object-level)                                             // M(f)(u) in the fibre
// -------------------------------------------------------------------------------------------------

/*
  For `M : B → Cat`, its Grothendieck total ∫M has:
    - objects: (x : Obj(B), u : Obj(M(x)))
    - 1-cells: (f : x → y in B,  α : M(f)(u) → v in M(y))

  Usual notation (covariant / opfibration-style):
    - write `M : B ⟶ Cat` (a strict functor for now),
    - write `∫ M` for the Grothendieck construction (category of elements / total category),
    - objects: `(x,u)` with `x ∈ Ob(B)` and `u ∈ Ob(M(x))`,
    - morphisms: `(f,α) : (x,u) → (y,v)` with `f : x → y` in `B` and `α : f_!(u) → v` in `M(y)`,
      where `f_!(u)` denotes the transported object `M(f)(u)` in the fibre over `y`.

  To make identity and composition *typecheck* by definitional equality, we introduce an explicit
  “transport on objects” operation `fib_cov_tapp0_fapp0` and give it strict functoriality rules on
  objects (preservation of identities and composition).

  This is intentionally strict for now (non-lax), as requested; later we can relax it by replacing
  these rules with higher-cell data (laxity 2-cells).
*/

// Transport objects in the fibre along a base 1-cell (covariant).                                    // M(f) on objects
// Usual notation: `f_!(u)` or `M(f)(u)` (opfibration / covariant transport on objects).               // f_! : M(x) → M(y) (on objects)
sequential symbol fib_cov_tapp0_fapp0 : Π [B : Cat] (M : τ (Obj (Functor_cat B Cat_cat))),
  Π [x y : τ (Obj B)], Π (f : τ (Obj (@Hom_cat B x y))), Π (u : τ (Obj (fapp0 M x))),
  τ (Obj (fapp0 M y));

// Canonicalization: compute (M(f))(u) *towards* `fib_cov_tapp0_fapp0 M f u`.                             // fold transport0
// Usual notation: `M(f)(u) ↦ f_!(u)`.                                                                 // fold to the transport head
// This keeps `fib_cov_tapp0_fapp0` as the stable head symbol (like `comp_fapp0`), so later
// object-level functoriality rules apply without unfolding.
rule fapp0 (fapp0 (@fapp1_func $B Cat_cat $M $x $y) $f) $u
  ↪ @fib_cov_tapp0_fapp0 $B $M $x $y $f $u;

// Strict functoriality on objects: M(id)(u) ↪ u.                                                      // preserves identities on objects
// Usual notation: `(id_x)_!(u) = u`.                                                                  // id_! = id
rule @fib_cov_tapp0_fapp0 $B $M $x $x (id $B $x) $u ↪ $u;

// Strict functoriality on objects (cut-elimination direction): M(g)(M(f)(u)) ↪ M(g∘f)(u).             // fold transport along ∘
// Usual notation: `g_!(f_!(u)) = (g ∘ f)_!(u)`.                                                       // g_!∘f_! ↪ (g∘f)_!
rule @fib_cov_tapp0_fapp0 $B $M $y $z $g (@fib_cov_tapp0_fapp0 $B $M $x $y $f $u)
  ↪ @fib_cov_tapp0_fapp0 $B $M $x $z (@comp_fapp0 $B $x $y $z $g $f) $u;

/*
  Fibre action as a functor (swap arguments / “module action”, ω-style)

  Given a Cat-valued functor M : B → Cat_cat, a base object x : Obj(B), and a fibre object u : Obj(M(x)),
  we want the induced functor

    fib_cov_tapp0_func(M,x,u,y) : Hom_B(x,y) → M(y)

  sending f : x→y to M(f)(u). In our encoding, M(f)(u) is normalized to the stable head
  `fib_cov_tapp0_fapp0 M f u` (see the folding rule above).

  Crucially, this *is* functorial in higher cells: a 2-cell α : f ⇒ g in the hom-category Hom_B(x,y)
  is mapped to the morphism in M(y) obtained by:
    (1) transporting α along M's hom-action to get a natural transformation M(f) ⇒ M(g),
    (2) evaluating that transformation at u (using `tapp0_fapp0`).
*/

// -------------------------------------------------------------------------------------------------
// 10b. Grothendieck totals: objects and π₁ (needed early for other computation rules)                 // ∫M objects
// -------------------------------------------------------------------------------------------------

// Objects of ∫M are Σ (x : Obj(B)), Obj(M(x)), but **only** for Grothendieck totals.                  // Σ-object description (Grothendieck only)
// For a general `E : Catd B` (semantic “category over B”), objects of `Total_cat E` are not
// definitionally a Σ-type: `Total_cat` is primitive data carried by `E`.
rule τ (Obj (Total_cat (@Fibration_cov_catd $B $M)))
  ↪ `τΣ_ x : τ (Obj $B), Obj (fapp0 $M x);                                                             // τ Obj(∫M) ↪ Σ x:B, Obj(M(x))

// The base projection π₁ : ∫M → B sends (x,u) ↦ x.                                                     // compute π₁ on objects (Grothendieck)
rule fapp0 (Total_proj1_func (Fibration_cov_catd $M)) (Struct_sigma $x $u) ↪ $x;

// NOTE (orientation update):
// With the outward normalization `Total_cat(Op_catd E) ↪ Op_cat(Total_cat E)` and `Obj(Op_cat A) ↪ Obj A`,
// objects of contravariant Grothendieck totals are *derivable* (definitionally) from the usual Σ-object
// rule for `Total_cat(Fibration_cov_catd ...)`. If performance ever regresses, a specialized “shortcut”
// rule for this shape can be reintroduced here.

// Dependent projection π₂ as a dependent functor into the pulled-back family over ∫M.               // second projection (displayed)
injective symbol Total_proj2_funcd [B : Cat] (E: Catd B) :                                             // dependent object: section over ∫E
  τ (Obj (Functord_cat (Terminal_catd (Total_cat E)) (Pullback_catd E (Total_proj1_func E))));            // π₂ : 1_{∫E} ⇒ (π₁)^*E

// General “context intro” for totals: a displayed functor over a base functor xy induces a functor between totals. // ∫-intro over xy
// Slice-style (over a fixed base) is recovered by taking xy := id_func and using Pullback_catd _ xy ↪ _.          // over-id specialization
injective symbol Total_intro_func :
  Π [X Y : Cat] [E : Catd X] [D : Catd Y] (xy : τ (Obj (Functor_cat X Y))),
    τ (Obj (Functord_cat E (Pullback_catd D xy)))
      → τ (Obj (Functor_cat (Total_cat E) (Total_cat D)));

// Packaged version: Total_intro as a functor in the displayed-functor argument FF.                     // FF ↦ (∫FF)
// This is the direct analogue of the tapp/tdapp “packaging + β-rule” pattern used elsewhere.          // stable head for higher structure in FF
injective symbol Total_intro_func_func :
  Π [X Y : Cat] [E : Catd X] [D : Catd Y] (xy : τ (Obj (Functor_cat X Y))),
    τ (Obj (Functor_cat
      (Functord_cat E (Pullback_catd D xy))
      (Functor_cat (Total_cat E) (Total_cat D))));

/*
  Important design note (what computes so far, and what is still TODO):

  There are two different “hom-actions” one might want to compute for total-introduction:

  (1) Functoriality in the *displayed functor argument* FF:
      Total_intro_func_func(xy) : Functord_cat(E, xy^*D) ⟶ Functor_cat(∫E, ∫D).
      Its hom-action sends a displayed transfor ϵ : FF ⇒ GG to a transfor between induced functors
        (∫FF) ⇒ (∫GG).
      This will be the right place to connect later to `Transfd_cat` / `tapp*`/`tdapp*`.

  (2) Functoriality of the *induced functor on totals* (in the base category X):
      For fixed xy and FF, the object (∫FF) : Functor_cat(∫E,∫D) has a hom-action
        fapp1_func(∫FF) : Hom_{∫E} → Hom_{∫D}.
      In particular, in the “section into a Grothendieck total” case (E = 1_X, D = ∫M),
      we currently have an object-level computation rule for fapp0(∫FF),
      but we do NOT yet have a corresponding computation rule for fapp1_func(∫FF).

  The missing ingredient for (2) is a stable-head projection extracting, from
    FF : 1_X → xy^*(∫M),
  the “fibre component over a base arrow g:x→x'”, i.e. the α in the Grothendieck Σ-morphism (f,α).
  This is *not* what the current `fdapp1_funcd` provides: `fdapp1_funcd` is about action on dependent-hom
  (via `homd_cov`) and belongs to the higher/simplicial layer.
*/

// β-rule: object-action of Total_intro_func_func is Total_intro_func.                                  // unpack Total_intro_func_func at objects
rule @fapp0
    _
    _
    (@Total_intro_func_func $X $Y $E $D $xy)
    $FF
  ↪ @Total_intro_func $X $Y $E $D $xy $FF;

// Sanity: the β-rule is visible as definitional equality.                                               // exercise Total_intro_func_func β-rule
assert [X Y : Cat] [E : Catd X] [D : Catd Y] (xy : τ (Obj (Functor_cat X Y)))
  (FF : τ (Obj (Functord_cat E (Pullback_catd D xy)))) ⊢
  @fapp0
    (Functord_cat E (Pullback_catd D xy))
    (Functor_cat (Total_cat E) (Total_cat D))
    (@Total_intro_func_func X Y E D xy)
    FF
  ≡ @Total_intro_func X Y E D xy FF;

// Terminal displayed functor into the terminal family (slice-style).                                 // unique map A → 1_X in Catd(X)
injective symbol Terminal_funcd : Π [B : Cat] (E : Catd B), τ (Obj (Functord_cat E (Terminal_catd B)));

// Terminal comprehension laws (cartierSolution13: Context_cat/Context_elimCat/Context_intro).        // ∫(1_X) ≡ X, π₁ ≡ id
rule Total_cat (Terminal_catd $A) ↪ $A;                                                               // ∫(1_A) ↪ A
rule Total_proj1_func (Terminal_catd $A) ↪ @id_func $A;                                        // π₁ : ∫(1_A)→A ↪ id_A

// Pullback preserves terminal displayed categories.                                                  // F^*(1_B) ≡ 1_A
rule @Pullback_catd $A $B (Terminal_catd $B) $F ↪ Terminal_catd $A;

// The dependent projection π₂ is the identity section when M is terminal.                            // π₂ : 1_{∫1} ⇒ (π₁)^*1  ↪ id
rule Total_proj2_funcd (Terminal_catd $A) ↪ @id_funcd $A (Terminal_catd $A);

// Intro rules: functor between totals induced by a displayed functor in the slice.                   // Context_intro_func analogues
// Identity: over id_X, the induced functor on totals is identity.                                      // ∫(id) ↪ id
// NOTE: we match on `id Cat_cat X` (not `id_func X`) because `id_func` is a definitional abbreviation.  // stable matching
rule @Total_intro_func $X $X $A $A (@id Cat_cat $X) (@id_funcd $X $A) ↪ @id_func (Total_cat $A);

// Terminal: over xy : X→Y, the induced functor into ∫(1_Y)≡Y is xy ∘ π₁.                               // ∫(!) ↪ xy∘π₁
rule @Total_intro_func $X $Y $A (Terminal_catd $Y) $xy (Terminal_funcd $A)
  ↪ @comp_fapp0 Cat_cat (Total_cat $A) $X $Y $xy (Total_proj1_func $A);

// β-like law: composing the induced functor with the projection of B gives the projection of A.      // (∫FF);π₁_B = π₁_A
// General projection law: (∫FF);π₁_D = (xy)∘(π₁_E).                                                     // projection naturality
rule @comp_fapp0 Cat_cat (Total_cat $E) (Total_cat $D) $Y (Total_proj1_func $D)
    (@Total_intro_func $X $Y $E $D $xy $FF)
  ↪ @comp_fapp0 Cat_cat (Total_cat $E) $X $Y $xy (Total_proj1_func $E);

// -------------------------------------------------------------------------------------------------
// 12. Terminal category and “constant functors from the terminal”                                   // 1 and points as functors
// -------------------------------------------------------------------------------------------------

// The terminal category 1 (one object, one morphism).                                                // categorical unit
// (Declared earlier as a forward declaration.)

// Terminal category is self-dual.                                                                    // 1ᵒᵖ ≡ 1
rule Op_cat Terminal_cat ↪ Terminal_cat;

// Objects of the terminal category are definitionally the unit type.                                 // Obj(1) ≡ 1
rule Obj Terminal_cat ↪ Unit_grpd;

// Every hom-category in the terminal category is terminal.                                           // Hom_1(*,*) ≡ 1
rule @Hom_cat Terminal_cat _ _ ↪ Terminal_cat;

// The unique functor A → 1 (terminal functor).                                                       // ! : A → 1
injective symbol Terminal_func : Π (A : Cat), τ (Obj (Functor_cat A Terminal_cat));                      // object of Functor_cat(A,1)

// Opposite of the terminal functor is the terminal functor out of Aᵒᵖ.                                // (!:A→1)ᵒᵖ ≡ !:Aᵒᵖ→1
rule @Op_func _ _ (@Terminal_func $A) ↪ @Terminal_func (Op_cat $A);

// Distinguished object * : Obj(1) (everything is definitionally equal to it via rules if desired).  // point of the terminal category
constant symbol Terminal_obj : τ (Obj Terminal_cat);                                                 // * : Obj(1)

// Identities and composition in the terminal category are the unique object.                         // id_* = * and *∘* = *
rule @id Terminal_cat _ ↪ Terminal_obj;
rule @comp_fapp0 Terminal_cat _ _ _ _ _ ↪ Terminal_obj;

// “Object as functor”: an object y:Obj(Y) induces a functor 1 → Y selecting y.                       // points as functors
injective symbol Obj_func : Π [Y : Cat], τ (Obj Y) → τ (Obj (Functor_cat Terminal_cat Y));               // y ↦ (1→Y) picking y

// Packaged version: y ↦ Obj_func(y) as an object in a functor category.                               // Y → Functor_cat(1,Y)
// Motivation: consistent with the “stable head” pattern used throughout emdash2 (e.g. tapp0_func),
// and useful once we want to talk about higher structure (transformations) *between* point-functors
// uniformly as morphisms in functor categories.
injective symbol Obj_func_func : Π [Y : Cat],
  τ (Obj (Functor_cat Y (Functor_cat Terminal_cat Y)));

// β-rule: applying Obj_func_func at y gives the point-functor Obj_func(y).                            // unpack Obj_func_func at objects
rule @fapp0 $Y (Functor_cat Terminal_cat $Y) (@Obj_func_func $Y) $y ↪ @Obj_func $Y $y;

// Opposite of a point-functor is the point-functor into the opposite category.                       // (y:1→Y)ᵒᵖ : 1→Yᵒᵖ
rule @Op_func _ _ (@Obj_func $Y $y) ↪ @Obj_func (Op_cat $Y) $y;

// Computation: applying the point-functor to the unique object of 1 yields the point.                // evaluation at *
rule fapp0 (Obj_func $F) $M ↪ $F;                                                                    // (const F)(*) ↪ F (for any * in 1)

// Sanity: Obj_func_func is definitionally the packaging of Obj_func.                                  // exercise Obj_func_func β-rule
assert [Y : Cat] (y : τ (Obj Y)) ⊢
  @fapp0 Y (Functor_cat Terminal_cat Y) (@Obj_func_func Y) y ≡ @Obj_func Y y;

// Sanity: the intended definitional computations for `Terminal_cat` fire.                            // unit tests
assert ⊢ τ (Obj Terminal_cat) ≡ unit;
assert (x y : τ (Obj Terminal_cat)) ⊢ @Hom_cat Terminal_cat x y ≡ Terminal_cat;
assert (x : τ (Obj Terminal_cat)) ⊢ @id Terminal_cat x ≡ Terminal_obj;
assert (x y z : τ (Obj Terminal_cat))
  (g : τ (Obj (@Hom_cat Terminal_cat y z))) (f : τ (Obj (@Hom_cat Terminal_cat x y))) ⊢
  @comp_fapp0 Terminal_cat x y z g f ≡ Terminal_obj;

// -------------------------------------------------------------------------------------------------
// 12b. Constant displayed categories over the terminal base                                         // “cast” Cat ↦ Catd(1)
// -------------------------------------------------------------------------------------------------

/*
  Goal (architecture):

  - We keep *both*:
      Functor_cat(A,B)    : Cat          (ordinary functors)
      Functord_cat(E,D)   : Cat          (displayed functors over a fixed base)
    because they support different primitive operations (`fapp0/fapp1_func` vs `fdapp0/...`).

  - But we want a cheap way to *embed* the ordinary world into the displayed world,
    so that later we can define special cases (like Transf_cat) via the general dependent notion
    (Transfd_cat), avoiding duplicate “parallel” definitions.

  The terminal base 1 is the simplest bridge:
    A : Cat    ↦    Lift_catd(A) : Catd(1)
  i.e. the constant fibration over the terminal category.
*/

// View an ordinary category as a displayed category over the terminal base.                          // constant family over 1
injective symbol Lift_catd : Cat → Catd Terminal_cat;                                                // A ↦ const_1(A)

// Opposite of a constant family is constant on the opposite category.                                // const(A)ᵒᵖ ≡ const(Aᵒᵖ)
rule @Op_catd Terminal_cat (Lift_catd $A) ↪ Lift_catd (Op_cat $A);

// The Grothendieck construction of a constant family over 1 is definitionally the original category. // ∫(const_1(A)) ≡ A
rule Total_cat (Lift_catd $A) ↪ $A;

// The base projection of ∫(const_1(A)) → 1 is the terminal functor A → 1.                            // π₁ ↪ !
rule Total_proj1_func (Lift_catd $A) ↪ Terminal_func $A;

// Fibres of a constant family are constant (independent of the base point in 1).                    // fibre(const_1(A),*) ≡ A
rule Fibre_cat (Lift_catd $A) _ ↪ $A;

// Lift an ordinary functor to a displayed functor between constant families over 1.                 // Functor ↦ displayed Functor over 1
injective symbol Lift_funcd : Π [A B : Cat],
  τ (Obj (Functor_cat A B)) → τ (Obj (Functord_cat (Lift_catd A) (Lift_catd B)));

// Forget a displayed functor between constant families by taking its induced functor on totals.     // displayed-over-1 ↦ ordinary
symbol Unlift_func [A B : Cat]
  (FF : τ (Obj (Functord_cat (Lift_catd A) (Lift_catd B)))) : τ (Obj (Functor_cat A B))
≔ @Total_intro_func Terminal_cat Terminal_cat (Lift_catd A) (Lift_catd B) (@id Cat_cat Terminal_cat) FF;
// NOTE: definitional abbreviation; keep in mind the same “rewrite head” principle as for `tapp0_fapp0` if we later want to normalize by rewriting at `Unlift_func ...`.

// // β-law: unlift∘lift is definitional (on functors).                                                  // ∫(lift(F)) ↪ F
rule @Total_intro_func Terminal_cat Terminal_cat (Lift_catd $A) (Lift_catd $B) (@id Cat_cat Terminal_cat) (@Lift_funcd $A $B $F)
  ↪ $F;


// -------------------------------------------------------------------------------------------------
// 13. Binary products of categories                                                                  // A×B
// -------------------------------------------------------------------------------------------------

// Product of categories (binary product in Cat).                                                     // categorical product
injective symbol Product_cat : Π (A1 A2 : Cat), Cat;                                         // A1 × A2 : Cat

// Objects of a product category are definitionally Σ-pairs.                                          // Obj(A×B) ≡ Obj(A)×Obj(B)
rule Obj (Product_cat $A1 $A2)
  ↪ @Σ_ (Obj $A1) (λ _ : τ (Obj $A1), Obj $A2);

/*
  Product_cat design notes (emdash2)

  We intentionally keep *two* views of products simultaneously:

  (1) Object/arrow (“singleton object”) view:
      - objects are Σ-pairs (constructor `Struct_sigma`, projections `sigma_{Fst,Snd}`)
      - arrows (objects of hom-categories) are paired by *the same* Σ-structure,
        once we compute Hom-categories of the product:
            Hom_{A×B}((X1,X2),(Y1,Y2))  ≡  Hom_A(X1,Y1) × Hom_B(X2,Y2)

  (2) Functor/transformation view (universal property):
      - on objects in functor categories: `Product_pair_func` and `Product_proj{L,R}_func`
      - on 2-cells / transfors: `Product_pair_transf` and `Product_proj{L,R}_transf`

  Both are kernel-useful:
  - the object/arrow view supports pointwise computation rules (identities/composition, etc.)
  - the functor/transformation view supports “Hom_Cat(X, A×B) ≃ Hom_Cat(X,A)×Hom_Cat(X,B)” reasoning
    while keeping `Functor_cat` primitive (so `fapp0/fapp1_func` remain well-typed).
*/

// Opposite distributes over binary products.                                                         // (A×B)ᵒᵖ ≡ Aᵒᵖ×Bᵒᵖ
rule Op_cat (Product_cat $A1 $A2) ↪ Product_cat (Op_cat $A1) (Op_cat $A2);

// Functorial projections (as functors out of any B): precomposition with π₁, π₂.                     // (−)∘πᵢ on functor categories
symbol Product_projL_func : Π [A1 A2 B: Cat], τ (Obj (Functor_cat B (Product_cat A1 A2))) →               // given H : B → (A1×A2)
  τ (Obj (Functor_cat B A1));                                                                            // obtain π₁∘H : B → A1
symbol Product_projR_func : Π [A1 A2 B: Cat], τ (Obj (Functor_cat B (Product_cat A1 A2))) →               // given H : B → (A1×A2)
  τ (Obj (Functor_cat B A2));                                                                            // obtain π₂∘H : B → A2

// Pairing of functors: given F:B→A1 and G:B→A2, build ⟨F,G⟩:B→A1×A2.                                 // universal property at functor level
injective symbol Product_pair_func : Π [A1 A2 I : Cat] (F : τ (Obj (Functor_cat I A1))) (G : τ (Obj (Functor_cat I A2))), // inputs functors
  τ (Obj (Functor_cat I (Product_cat A1 A2)));                                                           // paired functor to product

// Object-level projections/pairing (implemented by Σ-structure operations).                           // components of product objects
symbol Product_projL [A1 A2 : Cat] (XY : τ (Obj (Product_cat A1 A2))) : τ (Obj A1)                     // π₁ on objects
≔ sigma_Fst XY;
symbol Product_projR [A1 A2 : Cat] (XY : τ (Obj (Product_cat A1 A2))) : τ (Obj A2)                     // π₂ on objects
≔ sigma_Snd XY;
injective symbol Product_pair [A1 A2 : Cat] (X : τ (Obj A1)) (Y : τ (Obj A2))                          // ⟨X,Y⟩ : Obj(A1×A2)
  : τ (Obj (Product_cat A1 A2))
≔ @Struct_sigma (Obj A1) (λ _ : τ (Obj A1), Obj A2) X Y;

// Internalized binary product as a functor in Cat: × : Cat_cat×Cat_cat → Cat_cat.                     // (A,B) ↦ A×B
// Usual notation: `× : Cat × Cat → Cat`, with (A,B) ↦ A×B.
// Packaged as an object of Functor_cat(Cat_cat×Cat_cat, Cat_cat) so we can postcompose Cat-valued
// functors `E,D : Z → Cat_cat` to get their pointwise product `z ↦ E(z)×D(z)`.
constant symbol prodCat_func : τ (Obj (Functor_cat (Product_cat Cat_cat Cat_cat) Cat_cat));

// Object-action: prodCat_func₀(A,B) ≡ A×B.                                                                // fapp0(prodCat_func,(A,B)) ↪ Product_cat(A,B)
rule @fapp0 (Product_cat Cat_cat Cat_cat) Cat_cat prodCat_func (Struct_sigma $A $B)
  ↪ Product_cat $A $B;

// Sanity: prodCat_func acts pointwise as categorical product.                                             // prodCat_func(A,B) = A×B
assert (A B : Cat) ⊢
  fapp0 prodCat_func (@Product_pair Cat_cat Cat_cat A B)
    ≡ Product_cat A B;

// Hom-categories of the product compute pointwise on projections.                                   // Hom_{A×B}(P,Q) ≡ Hom_A(π₁P,π₁Q) × Hom_B(π₂P,π₂Q)
rule @Hom_cat (Product_cat $A1 $A2) $P $Q
  ↪ Product_cat (@Hom_cat $A1 (sigma_Fst $P) (sigma_Fst $Q))
                (@Hom_cat $A2 (sigma_Snd $P) (sigma_Snd $Q));

// Identity and composition in a product category are computed componentwise (on paired endpoints).   // id and ∘ in A×B
rule @id (Product_cat $A1 $A2) (Struct_sigma $X1 $X2)
  ↪ Struct_sigma (@id $A1 $X1) (@id $A2 $X2);

rule @comp_fapp0 (Product_cat $A1 $A2)
  (Struct_sigma $X1 $X2) (Struct_sigma $Y1 $Y2) (Struct_sigma $Z1 $Z2)
  (Struct_sigma $g1 $g2) (Struct_sigma $f1 $f2)
  ↪ Struct_sigma (@comp_fapp0 $A1 $X1 $Y1 $Z1 $g1 $f1)
                 (@comp_fapp0 $A2 $X2 $Y2 $Z2 $g2 $f2);

// Compatibility between Obj_func (points) and product structure (pointwise pairing/projections).     // evaluation coherence
rule Product_pair_func (Obj_func $X) (Obj_func $Y) ↪ Obj_func (Struct_sigma $X $Y);                  // ⟨x,y⟩ as functor from 1
rule Product_projL_func (Obj_func $XY) ↪ Obj_func (sigma_Fst $XY);                                   // π₁ on points-as-functors
rule Product_projR_func (Obj_func $XY) ↪ Obj_func (sigma_Snd $XY);                                   // π₂ on points-as-functors

// β/η laws at the functor level (universal property in Cat, object part).                            // proj∘pair, pair∘⟨proj⟩
rule Product_projL_func (Product_pair_func $F $G) ↪ $F
with Product_projR_func (Product_pair_func $F $G) ↪ $G;
rule Product_pair_func (Product_projL_func $H) (Product_projR_func $H) ↪ $H;

// Pointwise action on objects/homs for paired/projection functors.                                    // compute fapp0/fapp1_func through products
rule fapp0 (Product_pair_func $F $G) $x ↪ Struct_sigma (fapp0 $F $x) (fapp0 $G $x);
rule fapp0 (Product_projL_func $H) $x ↪ sigma_Fst (fapp0 $H $x);
rule fapp0 (Product_projR_func $H) $x ↪ sigma_Snd (fapp0 $H $x);

rule @fapp1_func _ _ (Product_pair_func $F $G) $X $Y
  ↪ Product_pair_func (@fapp1_func _ _ $F $X $Y) (@fapp1_func _ _ $G $X $Y);
rule @fapp1_func _ _ (Product_projL_func $H) $X $Y
  ↪ Product_projL_func (@fapp1_func _ _ $H $X $Y);
rule @fapp1_func _ _ (Product_projR_func $H) $X $Y
  ↪ Product_projR_func (@fapp1_func _ _ $H $X $Y);

// Transfor (natural transformation) operations: project/pair transfors pointwise.                   // 2-cells in Functor categories
symbol Product_projL_transf : Π [A1 A2 I : Cat],
  Π [F G : τ (Obj (Functor_cat I (Product_cat A1 A2)))],
  τ (Obj (Transf_cat F G)) → τ (Obj (Transf_cat (Product_projL_func F) (Product_projL_func G)));

symbol Product_projR_transf : Π [A1 A2 I : Cat],
  Π [F G : τ (Obj (Functor_cat I (Product_cat A1 A2)))],
  τ (Obj (Transf_cat F G)) → τ (Obj (Transf_cat (Product_projR_func F) (Product_projR_func G)));

symbol Product_pair_transf : Π [A1 A2 I : Cat],
  Π [F1 G1 : τ (Obj (Functor_cat I A1))],
  Π [F2 G2 : τ (Obj (Functor_cat I A2))],
  τ (Obj (Transf_cat F1 G1)) → τ (Obj (Transf_cat F2 G2))
    → τ (Obj (Transf_cat (Product_pair_func F1 F2) (Product_pair_func G1 G2)));

// -------------------------------------------------------------------------------------------------
// 14. Fibrewise products (products of displayed categories)                                         // displayed/product fibrations
// -------------------------------------------------------------------------------------------------

/*
  Recent addition (emdash2): making fibrewise products computable in the Grothendieck case.

  Semantics:
    - For general `U,A : Catd Z` (categories over Z), `Product_catd U A` is only a *fibrewise* product:
        (U×_Z A)(z) = U(z) × A(z)                                              (on fibres)
      but there is no canonical description of *morphisms over non-identity base arrows* unless we
      assume extra opfibration structure.

    - For Grothendieck displayed categories `Fibration_cov_catd E` coming from `E : Z ⟶ Cat`, we do
      have canonical Σ-descriptions of objects and morphisms in their total categories ∫E.

  Implementation:
    - We internalize categorical product as `prodCat_func : Cat×Cat ⟶ Cat` and introduce a primitive
      head `prodFib` for pointwise product of Cat-valued functors.
    - Then we add the key computation rule:
        Product_catd( Fibration_cov_catd E, Fibration_cov_catd D )  ↪  Fibration_cov_catd (prodFib E D)
      i.e. (∫E) ×_Z (∫D) is again a Grothendieck construction of the pointwise product functor.
*/

// Product of dependent categories over the same base Z (fibrewise product).                          // displayed product
injective symbol Product_catd : Π [Z : Cat] (U A : Catd Z), Catd Z;                       // U×A : Catd(Z)
rule Fibre_cat (Product_catd $U $A) $xZ ↪ Product_cat (Fibre_cat $U $xZ) (Fibre_cat $A $xZ);         // fibre(U×A,x) ↪ fibre(U,x)×fibre(A,x)

// Opposite distributes over fibrewise products.                                                      // (U×A)ᵒᵖ ≡ Uᵒᵖ×Aᵒᵖ
rule @Op_catd $Z (Product_catd $U $A)
  ↪ @Product_catd (Op_cat $Z) (@Op_catd $Z $U) (@Op_catd $Z $A);

// Pointwise product of Cat-valued functors.                                                           // (E⊗D)(z) = E(z)×D(z)
// Usual notation: for `E,D : Z ⟶ Cat`, define `(E × D) : Z ⟶ Cat` by `(E×D)(z) = E(z) × D(z)`.
// Design note: `prodFib` is a primitive *rewrite head* (not a definitional abbreviation).           // keep a stable head for rewriting
// Motivation (same pattern as `tapp0_fapp0` and `fib_cov_tapp0_fapp0`):
//   - A definition `prodFib E D ≔ (prodCat_func) ∘ ⟨E,D⟩` would expand to a large `comp_fapp0`
//     term in `Cat_cat`, which is expensive/fragile to unfold inside other rewrite rules.
//   - Making `prodFib` primitive gives a small, stable head so rules like
//       Product_catd(∫E,∫D) ↪ ∫(E×D)
//     can fire without forcing Lambdapi to normalize a big functor-composition expression.
symbol prodFib [Z : Cat]
  (E D : τ (Obj (Functor_cat Z Cat_cat))) : τ (Obj (Functor_cat Z Cat_cat));

// Pointwise computation on objects: (E×D)(z) ↦ E(z)×D(z).                                             // fapp0(prodFib(E,D),z) ↪ Product_cat(E(z),D(z))
rule fapp0 (prodFib $E $D) $z ↪ Product_cat (fapp0 $E $z) (fapp0 $D $z);

// Sanity: prodFib agrees pointwise with postcomposition by prodCat_func.                                // (E×D)(z) = prodCat_func(E(z),D(z))
assert [Z : Cat] (E D : τ (Obj (Functor_cat Z Cat_cat))) (z : τ (Obj Z)) ⊢
  fapp0 (prodFib E D) z ≡ fapp0 prodCat_func (Struct_sigma (fapp0 E z) (fapp0 D z));

// Fibrewise product of Grothendieck displayed categories is Grothendieck of pointwise product.        // ∫E ×_Z ∫D  ≅  ∫(E×D)
// If `E,D : Z ⟶ Cat` are Cat-valued functors, then their Grothendieck constructions are displayed
// categories `Fibration_cov_catd E, Fibration_cov_catd D : Catd Z`. Their fibrewise product over `Z`
// is again a Grothendieck displayed category, classified by the pointwise product functor:
//   (E ⊗ D)(z) = E(z) × D(z).
rule @Product_catd $Z (@Fibration_cov_catd $Z $E) (@Fibration_cov_catd $Z $D)
  ↪ @Fibration_cov_catd $Z (prodFib $E $D);

// Displayed projections/pairing (dependent functors witnessing product structure).                   // displayed πᵢ and pairing
symbol Product_projL_functord : Π [Z : Cat] [U A : Catd Z], τ (Obj (Functord_cat (Product_catd U A) U));  // π₁ : U×A → U
symbol Product_projR_functord : Π [Z : Cat] [U A : Catd Z], τ (Obj (Functord_cat (Product_catd U A) A));  // π₂ : U×A → A
injective symbol Product_pair_functord : Π [Z : Cat] [U A B : Catd Z]                                 // pairing in displayed world
  (F : τ (Obj (Functord_cat B U))) (G : τ (Obj (Functord_cat B A))),                                         // sections into U and A
  τ (Obj (Functord_cat B (Product_catd U A)));                                                           // paired section into U×A

// -------------------------------------------------------------------------------------------------
// 15. Composition as a functor (uncurried / product form)                                           // internal composition map
// -------------------------------------------------------------------------------------------------

// The “composition morphism” as a functor out of a product of hom-categories.                        // functorial / internal
// Think: this is the cartierSolution13-style "parametric object in a context", but now in ω-form:
// it packages the entire operation as an object in a functor-category, so it can itself have higher structure.
symbol comp_func : Π [A : Cat], Π [X_A Y_A : τ (Obj A)], Π [Z_A: τ (Obj A)],        // ambient A and objects
  τ (Obj (Functor_cat (Product_cat (@Hom_cat A Y_A Z_A) (@Hom_cat A X_A Y_A)) (@Hom_cat A X_A Z_A)));                  // an object in the functor-category

// Computation: applying the composition functor to a pair (g,f) returns the composite g∘f.           // β-rule for composition functor
rule (fapp0 (@comp_func $A $X $Y $Z)) (Struct_sigma $g $f) ↪ @comp_fapp0 $A $X $Y $Z $g $f; // compose(g,f) ↪ g∘f

// Sanity check: the β-rule is visible at the level of definitional equality / conversion.            // exercise the rule
assert [A : Cat] [X Y : τ (Obj A)] [Z : τ (Obj A)]
  (g : τ (Obj (@Hom_cat A Y Z))) (f : τ (Obj (@Hom_cat A X Y))) ⊢
  fapp0 (@comp_func A X Y Z) (Struct_sigma g f) ≡ @comp_fapp0 A X Y Z g f;

// Composition of functors is composition in Cat_cat (a special case of comp_fapp0).                 // categorical composition in Cat
symbol comp_cat_fapp0 [A B : Cat] [C : Cat]                                                     // A,B,C : Cat
  (F : τ (Obj (Functor_cat B C))) (G : τ (Obj (Functor_cat A B))) : τ (Obj (Functor_cat A C))  // F∘G : Functor_cat(A,C)
≔ @comp_fapp0 Cat_cat _ _ _ F G;                                                               // compose in Cat_cat
// NOTE: definitional abbreviation; if we later want pointwise computation rules with head `comp_cat_fapp0`, refactor to an uninterpreted symbol + rewrite rules (cf. tapp0_fapp0).

// -------------------------------------------------------------------------------------------------
// 16. Draft: “simplicial” view on higher morphisms via slice-like dependent functors                // experiments / TODO zone
// -------------------------------------------------------------------------------------------------

// TODO: add morphism-action computation rules for `hom_con` (dual of the `hom_cov` postcomposition rule). // dual Yoneda, computational interface
// TODO: add  interchange/composition laws.          // ω-category axioms
// TODO: generalize to “stacking” (horizontal composition of 2-cells along a 1-cell).   // 2-simplex / 3-simplex diagrams

// Dependent Yoneda/hom for a dependent category: “Hom_cat in the fibre / in a slice”.                   // dependent hom (2-simplex / triangle classifier)
constant symbol homd_cov : Π [Z : Cat], Π [E : Catd Z], Π [W_Z : τ (Obj Z)]                               // base Z, displayed E, base object W_Z
  (W_EW : τ (Obj (Fibre_cat E W_Z))), Π [D : Catd Z], Π (FF : τ (Obj (Functord_cat D E))),                 // W in fibre, D another displayed cat, FF : D→E
  τ (Obj (Functor_cat
    (Total_cat (Product_catd D (Fibration_cov_catd (comp_cat_fapp0 op (hom_cov W_Z (@id_func Z))))))
    Cat_cat));                                                                                            // target category Cat_cat (Cat-valued functors)

// Application of a dependent functor on objects, fibrewise.                                         // fibred fapp0
symbol fdapp0 : Π [Z : Cat], Π [E D : Catd Z], Π (FF : τ (Obj (Functord_cat E D))),          // dependent functor FF : E→D
  Π [X_Z : τ (Obj Z)], τ (Obj (Fibre_cat E X_Z)) → τ (Obj (Fibre_cat D X_Z));                         // map objects in each fibre

// Section into a Grothendieck total (object-level computation).                                       // (x ↦ (xy(x), FF_x(*)))
// If D = ∫M is Grothendieck and FF : 1_X → xy^*(D) is a displayed functor over xy : X→B, then ∫FF sends:
//   x ↦ (xy(x), u_x)  where u_x = (FF on the unique terminal fibre object at x).                      // uses Fibre_cat(Terminal_catd,_) ≡ 1
rule @fapp0 $X (Total_cat (@Fibration_cov_catd $B $M))
    (@Total_intro_func $X $B (Terminal_catd $X) (@Fibration_cov_catd $B $M) $xy $FF) $x
  ↪ Struct_sigma
      (fapp0 $xy $x)
      (@fdapp0 $X (Terminal_catd $X) (@Pullback_catd $X $B (@Fibration_cov_catd $B $M) $xy) $FF $x Terminal_obj);

// Sanity: the computed object-level section satisfies π₁∘(∫FF) = xy definitionally.                   // projection on introduced Σ-pair
assert [X B : Cat]
  (M  : τ (Obj (Functor_cat B Cat_cat)))
  (xy : τ (Obj (Functor_cat X B)))
  (FF : τ (Obj (Functord_cat (Terminal_catd X) (Pullback_catd (Fibration_cov_catd M) xy))))
  (x  : τ (Obj X)) ⊢
  @fapp0
    (Total_cat (Fibration_cov_catd M))
    B
    (Total_proj1_func (Fibration_cov_catd M))
    (@fapp0
      X
      (Total_cat (Fibration_cov_catd M))
      (@Total_intro_func X B (Terminal_catd X) (Fibration_cov_catd M) xy FF)
      x)
  ≡ @fapp0 X B xy x;

/*
  Fibre_func (extract the induced functor on a fibre)

  A displayed functor `FF : Obj(Functord_cat(E,D))` lives over a *fixed* base `Z` (slice-style: over id_Z).
  It therefore induces, for every base object `X_Z : Obj(Z)`, an ordinary functor between the fibres:

    Fibre_func(FF, X_Z) : Fibre_cat(E, X_Z) ⟶ Fibre_cat(D, X_Z).

  We keep this as a *separate* head from `fdapp0`:
  - `fdapp0` is the fibrewise object-map (computational handle);
  - `Fibre_func` packages that map as an object of `Functor_cat`, so we can state equalities
    between functors (e.g. `fapp1_func` as a fibre of `fapp1_funcd`) without requiring extensionality.
*/
symbol Fibre_func : Π [Z : Cat], Π [E D : Catd Z], Π (FF : τ (Obj (Functord_cat E D))),
  Π (X_Z : τ (Obj Z)),
  τ (Obj (Functor_cat (Fibre_cat E X_Z) (Fibre_cat D X_Z)));

// β-rule (objects): applying the extracted fibre functor is exactly fdapp0.                           // unpack Fibre_func at objects
rule @fapp0 (Fibre_cat $E $X_Z) (Fibre_cat $D $X_Z) (@Fibre_func $Z $E $D $FF $X_Z) $u
  ↪ @fdapp0 $Z $E $D $FF $X_Z $u;

// Special case: fdapp0 of a lifted ordinary functor is ordinary object-application (fibrewise).      // fdapp0(lift(F)) ↪ fapp0(F)
// NOTE: after dropping injectivity of `Obj`, the implicit base/category parameters of `fdapp0`
// are no longer reliably inferred from `Lift_funcd $F`, so we pin down the intended specialization
// explicitly: base = Terminal_cat, E/D are constant families Lift_catd A/B.
rule @fdapp0 Terminal_cat (Lift_catd $A) (Lift_catd $B) (@Lift_funcd $A $B $F) _ $x
  ↪ @fapp0 $A $B $F $x;

// Pointwise computation rule for homd_cov (Grothendieck/Grothendieck case).                            // (z,(d,f)) ↦ Hom_{E(z)}(f_!(W), FF(d))
// Usual notation (opfibration-style, strict for now):
//   - E,D : Z ⟶ Cat, with Grothendieck totals ∫E, ∫D,
//   - W ∈ Ob(E(W_Z)),
//   - f : W_Z → z in Z (the “base edge”),
//   - d ∈ Ob(D(z)),
//   - FF : ∫D → ∫E over Z (displayed functor / morphism over id_Z),
// then the fibrewise “triangle” category at (z,d,f) is:
//   Hom_{E(z)}( f_!(W),  FF_z(d) ).
//
// Scope/intent:
//   This computation is only asserted when both E and D come from Grothendieck constructions
//   (`Fibration_cov_catd E0`, `Fibration_cov_catd D0`), because the transport `f_!(W)` uses the strict
//   opfibration-style object transport `fib_cov_tapp0_fapp0` induced by a Cat-valued functor.           // keep Catd semantic, compute only for ∫(−)
//
// Here the input object is written in the normal form produced by the Grothendieck/product rules:
//   (z,(d,f)) is encoded as `Struct_sigma z (Struct_sigma d f)`, where
//     • `z : Ob(Z)`,
//     • `d : Ob(D(z))`,
//     • `f : Ob(Hom_Z(W_Z, z))` (the base edge along which we transport W).
rule fapp0 (@homd_cov $Z (@Fibration_cov_catd $Z $E0) $W_Z $W
		              (@Fibration_cov_catd $Z $D0) $FF)
		            (Struct_sigma $z (Struct_sigma $d $f))
  ↪ @Hom_cat (fapp0 $E0 $z)
      (@fib_cov_tapp0_fapp0 $Z $E0 $W_Z $z $f $W)
      (@fdapp0 $Z (@Fibration_cov_catd $Z $D0) (@Fibration_cov_catd $Z $E0) $FF $z $d);

/*
  tapp0_func / tapp0_fapp0 (ordinary “component at Y”)

  This is the “textbook” projection that extracts, from a (lax) transfor ϵ : Transf_cat(F,G),
  its underlying 1-cell component at Y:
    ϵ_Y : Hom_cat(FY, GY).

  Implementation: evaluate the packaged dependent functor ϵ^Y (given by `tapp1_fapp0_funcd Y ϵ`) at the
  identity arrow id_Y : Hom_cat(Y,Y) (which is an object in the fibre of Hom_A(Y,-) over Y).

  Note: this only extracts the 1-cell component. The lax naturality *2-cell data* lives in the
  higher/fibred part of the story (via `homd_cov` and the action of ϵ^X on non-identity 2-cells).
*/

// For fixed Y, “evaluate at Y” is functorial in ϵ (a 3-cell/modification acts componentwise).        // evaluation at id_Y
symbol tapp0_func : Π [A B : Cat], Π [F_AB G_AB : τ (Obj (Functor_cat A B))],
  Π (Y_A : τ (Obj A)),
  τ (Obj (Functor_cat (Transf_cat F_AB G_AB)
         (@Hom_cat B (fapp0 F_AB Y_A) (fapp0 G_AB Y_A))));

// Object-action of `tapp0_func`: compute the 1-cell component ϵ_Y by evaluating ϵ^Y at id_Y.         // component extraction
symbol tapp0_fapp0 : Π [A B : Cat], Π [F_AB G_AB : τ (Obj (Functor_cat A B))],
  Π (Y_A : τ (Obj A)), Π (ϵ : τ (Obj (Transf_cat F_AB G_AB))),
  τ (Obj (@Hom_cat B (fapp0 F_AB Y_A) (fapp0 G_AB Y_A)));

/*
  Design note: `tapp0_fapp0` is intentionally *not* defined by `≔ ...`.

  Motivation:
  - In the 1-category development (emdash.lp), the “pointwise” operations (like component extraction)
    are *rewrite heads*, so we can later add computation rules directly on them (and keep proof scripts small).
  - If we made `tapp0_fapp0` a definitional abbreviation (`≔ fdapp0 ...`), then rewriting would first unfold it,
    and we would lose the ability to conveniently attach further rewrite rules to the head symbol `tapp0_fapp0`.

  Key point: being a rewrite head doesn’t force it to unfold; it just means we can attach rules to it.

  Hence, we declare `tapp0_fapp0` as a primitive operation and give its current computation as a rewrite rule.
*/

// Canonicalization: fold "evaluate ϵ^Y at id_Y" *towards* `tapp0_fapp0`.                               // fold component extraction
// This keeps `tapp0_fapp0` as the stable head, avoiding conversion blowups in later developments.
rule @fdapp0 $A
      (@Fibration_cov_catd $A (@hom_cov $A $Y_A $A (@id_func $A)))
      (@Fibration_cov_catd $A (@hom_cov $B (fapp0 $F_AB $Y_A) $A $G_AB))
      (@tapp1_fapp0_funcd $A $B $F_AB $G_AB $Y_A $ϵ)
      $Y_A
      (@id $A $Y_A)
  ↪ @tapp0_fapp0 $A $B $F_AB $G_AB $Y_A $ϵ;

// β-rule: `tapp0_fapp0` is definitionally the object-action of the functor `tapp0_func`.            // unpack tapp0_func at objects
rule fapp0 (@tapp0_func $A $B $F_AB $G_AB $Y_A) $ϵ ↪ @tapp0_fapp0 $A $B $F_AB $G_AB $Y_A $ϵ;

/*
  Vertical identity/composition of transfors, computed pointwise.

  Even without committing to a Σ/record encoding of `Obj(Transf_cat F G)`, we can still ensure that
  the *components* of identities/composites normalize in the expected way by giving rewrite rules for
  the projection `tapp0_fapp0`.

  Usual notation:
    - For ϵ : Nat(F,G), its component is ϵ_Y : Hom_B(FY, GY).
    - For vertical composition η ∘ ϵ : Nat(F,H) with ϵ : Nat(F,G), η : Nat(G,H),
      we have (η ∘ ϵ)_Y = η_Y ∘ ϵ_Y.
    - For the identity 1_F : Nat(F,F), we have (1_F)_Y = id_{F(Y)}.
*/

// Components of the identity transfor compute to identity morphisms in B.                              // (1_F)_Y ↪ id_{F(Y)}
rule @tapp0_fapp0 $A $B $F $F $Y (id (Functor_cat $A $B) $F)
  ↪ @id $B (@fapp0 $A $B $F $Y);

// Components of vertical composite transfors compute to vertical composition in B.                     // (η∘ϵ)_Y ↪ η_Y ∘ ϵ_Y
rule @tapp0_fapp0 $A $B $F $H $Y (@comp_fapp0 (Functor_cat $A $B) $F $G $H $η $ϵ)
  ↪ @comp_fapp0 $B
      (@fapp0 $A $B $F $Y)
      (@fapp0 $A $B $G $Y)
      (@fapp0 $A $B $H $Y)
      (@tapp0_fapp0 $A $B $G $H $Y $η)
      (@tapp0_fapp0 $A $B $F $G $Y $ϵ);

/*
  fib_cov_transf (ω-style “swap arguments”, as a transfor)

  This is the ω-analogue of `module_action` in emdash.lp, but in the Cat-valued setting:

    given M : B → Cat and a fibre object u ∈ M(x),
    we package the action f ↦ M(f)(u) as a transfor
      fib_cov_transf(M,x,u) : hom_cov(x,id) ⇒ M.

  Its “component at y” (in the sense of `tapp0_fapp0`) is the functor
    Hom_B(x,y) → M(y),
  and we define the derived helper `fib_cov_tapp0_func` to be precisely that component.

  Architecture note (subject to review):
  - `fib_cov_transf` is the primitive/naturality-style package (good for ω-iteration).
  - `fib_cov_tapp0_func` is *not* the “real content”; it is a stable-head *normal form* for the
    component functor, so we can attach object-/hom-action computation rules without forcing expansion
    of `tapp0_fapp0` into `fdapp0 ...` during conversion/subject-reduction checks.
  - If/when the transfor infrastructure becomes robust enough, we may be able to drop this extra head
    and compute directly on `tapp0_fapp0 (... fib_cov_transf ...)` instead.
*/

symbol fib_cov_transf : Π [B : Cat] (M : τ (Obj (Functor_cat B Cat_cat))),
  Π (x : τ (Obj B)), τ (Obj (fapp0 M x))
    → τ (Obj (Transf_cat (@hom_cov B x B (@id_func B)) M));

// Functorial “action on a fixed fibre object”: (y ↦ (f ↦ M(f)(u))).                                  // u ↦ (Hom(x,-) → M(-))
// NOTE: we keep `fib_cov_tapp0_func` as a *stable head* (like `fib_cov_tapp0_fapp0`) so we can attach
// object-/hom-action computation rules to it without forcing expansion of the underlying transfor.
symbol fib_cov_tapp0_func : Π [B : Cat] (M : τ (Obj (Functor_cat B Cat_cat))),
  Π [x y : τ (Obj B)], Π (u : τ (Obj (fapp0 M x))),
  τ (Obj (Functor_cat (@Hom_cat B x y) (fapp0 M y)));

// Component at y (as a functor in Cat_cat): (fib_cov_transf u)_y ↪ fib_cov_tapp0_func(u,y).      // unpack module_action at y
rule @tapp0_fapp0 $B Cat_cat (@hom_cov $B $x $B (@id_func $B)) $M $y (@fib_cov_transf $B $M $x $u)
  ↪ @fib_cov_tapp0_func $B $M $x $y $u;

// Object-action: apply M to f, then to u (folded to `fib_cov_tapp0_fapp0`).                              // f ↦ f_!(u)
rule fapp0 (@fib_cov_tapp0_func $B $M $x $y $u) $f
  ↪ @fib_cov_tapp0_fapp0 $B $M $x $y $f $u;

// Hom-action of fib_cov_tapp0_func (2-cells): evaluate M(α) at u.                                  // (fib_cov_tapp0_func)_1(α) = (M(α))_u
rule @fapp0 (@Hom_cat (@Hom_cat $B $x $y) $f $g)
    _
    (@fapp1_func (@Hom_cat $B $x $y) (fapp0 $M $y)
      (@fib_cov_tapp0_func $B $M $x $y $u) $f $g) $α
  ↪ @tapp0_fapp0 (fapp0 $M $x) (fapp0 $M $y)
      (fapp0 (@fapp1_func $B Cat_cat $M $x $y) $f)
      (fapp0 (@fapp1_func $B Cat_cat $M $x $y) $g)
      $u
      (@fapp0 (@Hom_cat (@Hom_cat $B $x $y) $f $g)
        _
        (@fapp1_func (@Hom_cat $B $x $y) (Functor_cat (fapp0 $M $x) (fapp0 $M $y))
          (@fapp1_func $B Cat_cat $M $x $y) $f $g) $α);

// -------------------------------------------------------------------------------------------------
// 10c. Grothendieck construction: homs and 1-cell structure (strict opfibration convention)           // homs in ∫M
// -------------------------------------------------------------------------------------------------

// Grothendieck hom family (opfibration convention).                                                    // f ↦ Hom_{M(y)}(M(f)(u),v)
// For fixed (x,u) and (y,v), this is a Cat-valued functor on the hom-category Hom_B(x,y).
// Usual notation: for fixed `u ∈ M(x)` and `v ∈ M(y)`, define
//   H_{u,v} : Hom_B(x,y) ⟶ Cat
//   H_{u,v}(f) = Hom_{M(y)}(f_!(u), v).                                                                // H_{u,v}(f) = Hom_{M(y)}(M(f)(u),v)
symbol Groth_hom_fam : Π [B : Cat] (M : τ (Obj (Functor_cat B Cat_cat))),
  Π [x y : τ (Obj B)], Π (u : τ (Obj (fapp0 M x))) (v : τ (Obj (fapp0 M y))),
  τ (Obj (Functor_cat (Op_cat (@Hom_cat B x y)) Cat_cat));

// Definable expansion (do NOT unfold by rewriting; keep `Groth_hom_fam` as a stable head for typing).  // avoids conversion blowups in homs of ∫M
// This is the intended definition:
//   Groth_hom_fam_def(u,v) = hom_con(v,id) ∘ (fib_cov_tapp0_func(u))^op.
symbol Groth_hom_fam_def [B : Cat] (M : τ (Obj (Functor_cat B Cat_cat)))
  [x y : τ (Obj B)] (u : τ (Obj (fapp0 M x))) (v : τ (Obj (fapp0 M y)))
  : τ (Obj (Functor_cat (Op_cat (@Hom_cat B x y)) Cat_cat))
≔ @comp_fapp0 Cat_cat
     (Op_cat (@Hom_cat B x y))
     (Op_cat (fapp0 M y))
     Cat_cat
     (@hom_con (fapp0 M y) v (fapp0 M y) (@id_func (fapp0 M y)))
     (@Op_func (@Hom_cat B x y) (fapp0 M y) (@fib_cov_tapp0_func B M x y u));

// β-rule: on objects f:x→y, Groth_hom_fam returns the fibre hom-category Hom_{M(y)}(M(f)(u),v).        // compute family at a base arrow
// Usual notation: `H_{u,v}(f) = Hom_{M(y)}(f_!(u), v)`.                                                // expand on objects
rule fapp0 (@Groth_hom_fam $B $M $x $y $u $v) $f
  ↪ @Hom_cat (fapp0 $M $y) (@fib_cov_tapp0_fapp0 $B $M $x $y $f $u) $v;

// Grothendieck hom-category is itself a Grothendieck total.                                            // Hom_{∫M}((x,u),(y,v)) ≡ ∫(f ↦ Hom_{M(y)}(M(f)(u),v))
// Usual notation (opfibration Grothendieck formula):
//   Hom_{∫M}((x,u),(y,v))  ≅  ∫_{f : x→y} Hom_{M(y)}(f_!(u), v).                                        // homs in ∫M as another ∫
// Grothendieck hom-category is itself a Grothendieck total (contravariant in the base hom-category).   // Hom_{∫M}((x,u),(y,v)) ≡ (∫H)^op
// Using Op-acrobatics: for H : (Hom_B(x,y))ᵒᵖ → Cat, we form ∫H over (Hom_B(x,y))ᵒᵖ and then take Op.    // keep 2-cell direction correct
rule @Hom_cat (Total_cat (@Fibration_cov_catd $B $M)) (Struct_sigma $x $u) (Struct_sigma $y $v)
  ↪ Op_cat (Total_cat
      (
        (@Fibration_cov_catd _ (@Groth_hom_fam $B $M $x $y $u $v))));

// Functoriality of the base projection on hom-categories (Grothendieck).                               // π₁₁ : Hom_{∫M} → Hom_B
// Usual notation: `π₁ : ∫M → B` induces on homs a functor
//   (π₁)_{1} : Hom_{∫M}((x,u),(y,v)) ⟶ Hom_B(x,y),
//   sending `(f,α)` to `f`.                                                                            // forget the fibre component
rule @fapp1_func (Total_cat (@Fibration_cov_catd $B $M)) $B (Total_proj1_func (Fibration_cov_catd $M))
  (Struct_sigma $x $u) (Struct_sigma $y $v)
  ↪ Op_func (Total_proj1_func
      (
        (@Fibration_cov_catd _ (@Groth_hom_fam $B $M $x $y $u $v))));

// The base projection on objects is the first Σ-projection.                                            // π₁(f,α)=f
rule fapp0
    (Total_proj1_func
      (@Op_catd _
        (@Fibration_cov_catd _ $H)))
    (Struct_sigma $f $α)
  ↪ $f;

// Sanity: object-level description of Hom_{∫M}((x,u),(y,v)) as a Σ-type.                                // 1-cells are pairs (f,α)
// NOTE (performance): this “fully expanded” assertion can be expensive to normalize during early development
// (it forces several layers of rewriting through totals/opposites/Grothendieck). Re-enable once the rewrite
// layer is stable enough that `make check` stays comfortably below the timeout.

assert [B : Cat] (M : τ (Obj (Functor_cat B Cat_cat)))
  (x y : τ (Obj B)) (u : τ (Obj (fapp0 M x))) (v : τ (Obj (fapp0 M y))) ⊢
  τ (Obj (@Hom_cat (Total_cat (@Fibration_cov_catd B M)) (Struct_sigma x u) (Struct_sigma y v)))
    ≡ `τΣ_ f : τ (Obj (@Hom_cat B x y)),
         Obj (@Hom_cat (fapp0 M y) (@fib_cov_tapp0_fapp0 B M x y f u) v);

// Sanity: π₁ sends a 1-cell (f,α) to its base arrow f.                                                 // projection on 1-cells
// This is the key “forget the fibre component” behavior of the Grothendieck projection on morphisms:
//   π₁(f,α) = f.
assert [B : Cat] (M : τ (Obj (Functor_cat B Cat_cat)))
  (x y : τ (Obj B)) (u : τ (Obj (fapp0 M x))) (v : τ (Obj (fapp0 M y)))
  (f : τ (Obj (@Hom_cat B x y)))
  (α : τ (Obj (@Hom_cat (fapp0 M y) (@fib_cov_tapp0_fapp0 B M x y f u) v))) ⊢
  fapp0
    (@fapp1_func (Total_cat (@Fibration_cov_catd B M)) B (Total_proj1_func (Fibration_cov_catd M))
      (Struct_sigma x u) (Struct_sigma y v))
    (Struct_sigma f α)
    ≡ f;

// Sanity: objects of Hom_{∫M}((x,u),(y,v)) reduce to Σ-pairs, via the previous rule + τ(Σ_) ↪ τΣ_.      // normalization smoke-test

// Identity/composition in ∫M (Grothendieck case, strict).                                               // id and ∘ on 1-cells of ∫M
//
// Objects of the hom-categories of ∫M are Σ-pairs (f,α) where:
//   - f : x → y is a 1-cell in the base B (i.e. an object of Hom_cat(B,x,y)),
//   - α : Hom_{M(y)}(f_!(u), v) is a 1-cell in the fibre over y.
//
// The rules below give the expected strict opfibration behavior:
//   id_(x,u)       = (id_x, id_u)
//   (g,β) ∘ (f,α)  = (g∘f,  β ∘ M(g)(α)).

rule @id (Total_cat (@Fibration_cov_catd $B $M)) (Struct_sigma $x $u)
  ↪ Struct_sigma
      (@id $B $x)
      (@id (fapp0 $M $x) $u);

rule @comp_fapp0 (Total_cat (@Fibration_cov_catd $B $M))
  (Struct_sigma $x $u) (Struct_sigma $y $v) (Struct_sigma $z $w)
  (Struct_sigma $g $β) (Struct_sigma $f $α)
  ↪ Struct_sigma
      (@comp_fapp0 $B $x $y $z $g $f)
      (@comp_fapp0 (fapp0 $M $z)
        (@fib_cov_tapp0_fapp0 $B $M $x $z (@comp_fapp0 $B $x $y $z $g $f) $u)
        (@fib_cov_tapp0_fapp0 $B $M $y $z $g $v)
        $w
        $β
        (@fapp0
          (@Hom_cat (fapp0 $M $y) (@fib_cov_tapp0_fapp0 $B $M $x $y $f $u) $v)
          (@Hom_cat (fapp0 $M $z)
            (@fib_cov_tapp0_fapp0 $B $M $x $z (@comp_fapp0 $B $x $y $z $g $f) $u)
            (@fib_cov_tapp0_fapp0 $B $M $y $z $g $v))
          (@fapp1_func
            (fapp0 $M $y)
            (fapp0 $M $z)
            (@fapp0
              (@Hom_cat $B $y $z)
              (Functor_cat (fapp0 $M $y) (fapp0 $M $z))
              (@fapp1_func $B Cat_cat $M $y $z)
              $g)
            (@fib_cov_tapp0_fapp0 $B $M $x $y $f $u)
            $v)
          $α));

/*
  Product_cat and transfors (componentwise computation)

  The following rules implement the expected “pairing/projection is pointwise” behavior at the level
  of 1-cell components of transfors (extracted by `tapp0_fapp0`):

    - projecting a transfor into A1×A2 yields a transfor into A1/A2 whose components are obtained by
      projecting the original components;
    - pairing transfors yields a transfor into A1×A2 whose components are paired.

  This is the minimal interface we need for later developments (exchange laws, adjunctions, etc.),
  even before the higher (lax) naturality 2-cell data is fully implemented.
*/

rule sigma_Fst (@tapp0_fapp0 $I (Product_cat $A1 $A2) $F $G $X $ϵ)
  ↪ @tapp0_fapp0 $I $A1
      (@Product_projL_func $A1 $A2 $I $F)
      (@Product_projL_func $A1 $A2 $I $G)
      $X
      (@Product_projL_transf $A1 $A2 $I $F $G $ϵ);

rule sigma_Snd (@tapp0_fapp0 $I (Product_cat $A1 $A2) $F $G $X $ϵ)
  ↪ @tapp0_fapp0 $I $A2
      (@Product_projR_func $A1 $A2 $I $F)
      (@Product_projR_func $A1 $A2 $I $G)
      $X
      (@Product_projR_transf $A1 $A2 $I $F $G $ϵ);

rule @tapp0_fapp0 $I (Product_cat $A1 $A2)
  (@Product_pair_func $A1 $A2 $I $F1 $F2)
  (@Product_pair_func $A1 $A2 $I $G1 $G2)
  $X
  (@Product_pair_transf $A1 $A2 $I $F1 $G1 $F2 $G2 $ϵ1 $ϵ2)
  ↪ Struct_sigma (@tapp0_fapp0 $I $A1 $F1 $G1 $X $ϵ1)
                 (@tapp0_fapp0 $I $A2 $F2 $G2 $X $ϵ2);

/*
  Placeholder for lax naturality (triangle 2-cell).

  The formulation we ultimately want for computation is the one expressed by the *dependent* packaging
  `tapp1_func_funcd`, i.e. by the “superscripted” components
    ϵ^X : Hom_A(X,-) ⇒ Hom_B(FX, G(-)).

  For fixed X and for composable arrows f : X → Y₁ and g : Y₁ → Y₂ in A, write the induced 1-cells
    ηᵋ_f      : FX → G(Y₁)     (obtained by evaluating ϵ^X at f)
    ηᵋ_{g∘f}  : FX → G(Y₂)     (obtained by evaluating ϵ^X at g∘f)
  Then laxness provides a *non-identity 2-cell* (a “triangle”) in the hom-category Hom_B(FX, G(Y₂)):

      G(g) ∘ ηᵋ_f   ⇒   ηᵋ_{g ∘ f}

  Important syntactic remark (why the left side says “G(g) ∘ …”):
  - In the *ambient* 2-category B, a 2-cell compares two parallel 1-cells with the same source/target.
    Here both sides must live in Hom_B(FX, G(Y₂)).
  - But ηᵋ_f has codomain G(Y₁), so to compare it with ηᵋ_{g∘f} (codomain G(Y₂)) we must first
    “transport along g” using G(g) : G(Y₁) → G(Y₂), yielding the composite G(g) ∘ ηᵋ_f : FX → G(Y₂).

  This is why the displayed/fibred reading is often better written with an explicit “over g” marker:

      ηᵋ_f   ⇒_g   ηᵋ_{g ∘ f}

  where “⇒_g” means: a 2-arrow in the fibre over the base edge g, whose *ambient* boundary is the
  transported comparison G(g) ∘ ηᵋ_f ⇒ ηᵋ_{g∘f}.

  This is the shape that `homd_cov` is meant to support: it is fibred over a base product whose points
  include (at least) the edge g and the 1-cell ηᵋ_{g∘f}, so the 2-arrow witnessing the triangle is “over g”.

  The earlier textbook boundary
      ηᵋ_{Y₂} ∘ F(g) ⇒ G(g) ∘ ηᵋ_{Y₁}
  is still a useful semantic sanity check, but it is not the computational driver for iteration here.
*/
constant symbol tapp_lax_triangle :
  Π [A B : Cat], Π [F_AB G_AB : τ (Obj (Functor_cat A B))],
  Π [X Y1 Y2 : τ (Obj A)],
  Π (f : τ (Obj (@Hom_cat A X Y1))), Π (g : τ (Obj (@Hom_cat A Y1 Y2))), Π (ϵ : τ (Obj (Transf_cat F_AB G_AB))),
  τ (Obj
      (@Hom_cat (@Hom_cat B (fapp0 F_AB X) (fapp0 G_AB Y2))
        // source 1-cell: G(g) ∘ ηᵋ_f  (transport ηᵋ_f along g so it lands in Hom_B(FX, GY₂))
        (@comp_fapp0 B (fapp0 F_AB X) (fapp0 G_AB Y1) (fapp0 G_AB Y2)
          (fapp0 (@fapp1_func A B G_AB Y1 Y2) g)
          (@fdapp0 A
            (Fibration_cov_catd (hom_cov X (@id_func A)))
            (Fibration_cov_catd (hom_cov (fapp0 F_AB X) G_AB))
            (@tapp1_fapp0_funcd A B F_AB G_AB X ϵ)
            Y1
            f))
        // target 1-cell: ηᵋ_{g∘f}
        (@fdapp0 A
          (Fibration_cov_catd (hom_cov X (@id_func A)))
          (Fibration_cov_catd (hom_cov (fapp0 F_AB X) G_AB))
          (@tapp1_fapp0_funcd A B F_AB G_AB X ϵ)
          Y2
          (@comp_fapp0 A X Y1 Y2 g f))));

// “Slice-category” / simplicial action (warm-up): fapp1_funcd packages fapp1_func as a dependent functor over representables. // 2-simplex intuition
// Motivation: complements the globular iteration (Hom_cat(X,Y) : Cat) with a simplicial iteration (fibrewise). // 2- and 3-simplex pictures
// NOTE: the “higher (3-)simplicial” viewpoint becomes most relevant later, once `homd_cov` is involved (see `fdapp1_funcd`). // relevance note
symbol fapp1_funcd : Π [A B : Cat], Π (F_AB : τ (Obj (Functor_cat A B))), Π [X_A: τ (Obj A)],         // functor and outer index
  τ (Obj (Functord_cat (Fibration_cov_catd (hom_cov X_A (@id_func A)))                              // source displayed: Hom_A(X_A,-)
                  (Fibration_cov_catd (hom_cov (fapp0 F_AB X_A) F_AB))));                                // target displayed: Hom_B(FX_A, F_AB(-))

// Fibrewise identification: the fibre of the displayed packaging is the usual hom-action functor.     // fapp1_func = Fibre_func(fapp1_funcd)
// Design note:
//   This is a functor-level slogan (“fapp1_func is the fibre of fapp1_funcd”), not just a pointwise fact.
//   It matters when later constructions expect functor objects as inputs (transfors/modifications), not merely their object-action.
rule @Fibre_func $A _ _ (@fapp1_funcd $A $B $F_AB $X_A) $Y_A
  ↪ @fapp1_func $A $B $F_AB $X_A $Y_A;

// Link: the object-action fdapp0 of fapp1_funcd reduces to applying fapp1_func on a morphism-object.           // coherence rule between globular & simplicial views
rule fdapp0 (@fapp1_funcd $A $B $F $X) [$Y] $f
  ↪ @fapp0 (@Hom_cat $A $X $Y)
      (@Hom_cat $B (fapp0 $F $X) (fapp0 $F $Y))
      (@fapp1_func $A $B $F $X $Y)
      $f;                                                        // fdapp0(fapp1_funcd(F,X),f) ↪ fapp0(fapp1_func(F,X,Y),f)

// id-instantiation (key normalization): identity natural transformation folds to functorial action on homs.     // stable head for "ϵ = id"
//
// Usual 1-categorical notation:
//   - Let F : A ⟶ B be a functor.
//   - Let 1_F : Nat(F,F) be the identity natural transformation.
//   - Fix X ∈ Obj(A). Then the “superscripted component packaging” gives a functor between representables:
//         (1_F)^X : Hom_A(X,−) ⟶ Hom_B(FX,F−)
//     and it sends an arrow f : X ⟶ Y to the arrow F(f) : FX ⟶ FY.
//
// In emdash2 notation:
//   - `tapp1_fapp0_funcd A B F F X (id (Functor_cat A B) F)` is the packaged (1_F)^X,
//   - `fapp1_funcd A B F [X]` is the stable-head packaging of “F on homs” with the same type,
// so we canonically rewrite the former to the latter.
rule @tapp1_fapp0_funcd $A $B $F $F $X (id (Functor_cat $A $B) $F)
  ↪ @fapp1_funcd $A $B $F $X;

// Sanity: the link rule fires at the level of definitional equality.                                            // exercise the rule
assert [A B : Cat] (F : τ (Obj (Functor_cat A B))) (X Y : τ (Obj A)) (f : τ (Obj (@Hom_cat A X Y))) ⊢
  fdapp0 (fapp1_funcd F [X]) [Y] f ≡ fapp0 (fapp1_func F [X] [Y]) f;

// Sanity: functor-level identification (needs Fibre_func; not derivable from pointwise equality alone).          // exercise Fibre_func rule
assert [A B : Cat] (F : τ (Obj (Functor_cat A B))) (X Y : τ (Obj A)) ⊢
  Fibre_func (fapp1_funcd F [X]) Y ≡ fapp1_func F [X] [Y];

// Application of a dependent functor on morphisms (still draft: depends on `homd_cov`).              // fibred fapp1_func
// If `homd_cov` is the “triangle/surface classifier”, then `fdapp1_funcd` is where the simplicial story starts in earnest:
// it should act on dependent-hom data that lives over base edges (and later higher simplices).
//
// A fibrewise ordinary functor can always be extracted by `Fibre_func (fdapp1_funcd F X_) p`, for a chosen base point `p`
// of the base category of those `Fibration_cov_catd (homd_cov ...)` terms. If this becomes too verbose inside rewrite rules,
// introduce a stable head specialized to the intended base point normal form (same “stable head” pattern as `tapp0_fapp0`, `prodFib`, etc.).
symbol fdapp1_funcd : Π [Z : Cat], Π [A B : Catd Z], Π (F : τ (Obj (Functord_cat A B))),          // dependent functor F : A→B
  Π [X_: τ (Obj Z)] (X: τ (Obj (Fibre_cat A X_))),                                                    // base object X_ and fibre object X
  τ (Obj (Functord_cat
    (Fibration_cov_catd (@homd_cov Z A X_ X A (@id_funcd Z A)))                                       // source hom in fibre (draft; homd_cov computes mainly in Grothendieck case)
    (Fibration_cov_catd (@homd_cov Z B X_ (@fdapp0 Z A B F X_ X) A F))));                              // target hom in fibre (draft; pending general homd_cov computation rules)

// Stable-head fibre functor extracted from `fdapp1_funcd` (for uniformity and readability).           // Fibre_func(fdapp1_funcd)
// This packages the fibrewise action as an ordinary functor between the corresponding fibre categories.
symbol fdapp1_func : Π [Z : Cat], Π [A B : Catd Z], Π (F : τ (Obj (Functord_cat A B))),
  Π [X_: τ (Obj Z)] (X: τ (Obj (Fibre_cat A X_))),
  Π (p : τ (Obj (Total_cat (Product_catd A (Fibration_cov_catd (comp_cat_fapp0 op (hom_cov X_ (@id_func Z)))))))),
  τ (Obj (Functor_cat
     (Fibre_cat (Fibration_cov_catd (@homd_cov Z A X_ X A (@id_funcd Z A))) p)
     (Fibre_cat (Fibration_cov_catd (@homd_cov Z B X_ (@fdapp0 Z A B F X_ X) A F)) p)));

// Folding rule (canonical head): the fibre functor extracted from `fdapp1_funcd` is named `fdapp1_func`. // fold Fibre_func(fdapp1_funcd)
// This mirrors the “warm-up” rule `Fibre_func(fapp1_funcd ...) ↪ fapp1_func ...`.
rule @Fibre_func
    _
    _
    _
    (@fdapp1_funcd $Z $A $B $F $X_ $X)
    $p
  ↪ @fdapp1_func $Z $A $B $F $X_ $X $p;

// β-rule (objects): object-action of `fdapp1_func` is `fdapp0` of `fdapp1_funcd` in the corresponding fibre. // unpack fdapp1_func at objects
rule @fapp0
    (Fibre_cat _ $p)
    (Fibre_cat _ $p)
    (@fdapp1_func $Z $A $B $F $X_ $X $p)
    $u
  ↪ @fdapp0
      _
      (Fibration_cov_catd _)
      (Fibration_cov_catd _)
      (@fdapp1_funcd $Z $A $B $F $X_ $X)
      $p
      $u;

// Dependent transformations between dependent functors (displayed natural transformations).          // displayed transfors
constant symbol Transfd_cat : Π [Z : Cat], Π [E D : Catd Z],                                 // base and displayed categories
  Π (FF GG : τ (Obj (Functord_cat E D))), Cat;                               // Transfd_cat(FF,GG) : Cat

// Key identification: the hom-category of the displayed-functor category is the displayed-transformation category.
// Hom_{Functord_cat(E,D)}(FF,GG) ≡ Transfd_cat(FF,GG) definitionally.                                  // definitional equality of homs
rule @Hom_cat (Functord_cat _ _) $F $G ↪ Transfd_cat $F $G;

/*
  tdapp1_func_funcd is the displayed analogue of tapp1_func_funcd.

  Again, the binders (X_Z, U_EX) are *external* projection indices:
  - X_Z : Obj(Z) picks a fibre of the displayed category E : Catd(Z),
  - U_EX : Obj(Fibre_cat E X_Z) is the point *inside that fibre* at which we project components.

  Think “superscripted component”: for ϵ : Transfd_cat(F,G), we get ϵ^(X_,X) as a dependent functor between
  displayed representables. This is the step that makes iteration possible:
  modifications between displayed transfors project to transfors between these component-functors, etc.

  Observation (common generalization; guided by types):

  `tdapp1_func_funcd` is a “single ancestor” of:
  - `fdapp1_funcd` (displayed functorial action on dependent-homs, packaged as a displayed functor):
      specialize to the identity displayed transfor ϵ := 1_FF : Transf_Z(FF,FF),
      then the packaged component (1_FF)^(X,U) is definitionally `fdapp1_funcd FF [X] U`
      (by the id-folding rule).

  - `tdapp0_func` (displayed pointwise component evaluation), which we define below:
      specialize the external indices to (X,U) := (Y,V) and then evaluate ϵ^(Y,V) at the “identity”
      in the corresponding displayed representable, yielding the component
        ϵ_{(Y,V)} : Hom_{D_Y}(FF_Y(V), GG_Y(V)).

  So `tdapp1_func_funcd` is the displayed “project-to-a-functor between displayed representables” operation,
  from which both “apply FF to dependent-hom data” and “extract the component ϵ_{(Y,V)}” arise.
*/
symbol tdapp1_func_funcd : Π [Z : Cat], Π [E D : Catd Z], Π [FF GG : τ (Obj (Functord_cat E D))],        // dependent functors FF,GG
Π (X_Z: τ (Obj Z)) (U_EX: τ (Obj (Fibre_cat E X_Z))),                                                  // component at fibre object U_EX
		   τ (Obj (Functor_cat (Transfd_cat FF GG)
		          (Functord_cat (Fibration_cov_catd (@homd_cov Z E X_Z U_EX E (@id_funcd Z E)))               // source hom (draft; see homd_cov notes)
		                    (Fibration_cov_catd (@homd_cov Z D X_Z (@fdapp0 Z E D FF X_Z U_EX) E GG)))));        // target hom (draft; pending full homd_cov normalization)

// `tdapp1_fapp0_funcd` is the fapp0 part of `tdapp1_func_funcd`
symbol tdapp1_fapp0_funcd : Π [Z : Cat], Π [E D : Catd Z], Π [FF GG : τ (Obj (Functord_cat E D))],        // dependent functors FF,GG
Π (X_Z: τ (Obj Z)) (U_EX: τ (Obj (Fibre_cat E X_Z))),                                                  // component at fibre object U_EX
  Π (ϵ : τ (Obj (Transfd_cat FF GG))),
  τ (Obj (Functord_cat (Fibration_cov_catd (@homd_cov Z E X_Z U_EX E (@id_funcd Z E)))               // source hom (draft; see homd_cov notes)
                  (Fibration_cov_catd (@homd_cov Z D X_Z (@fdapp0 Z E D FF X_Z U_EX) E GG))));         // target hom (draft; pending full homd_cov normalization)

// β-rule: `tdapp1_fapp0_funcd` is definitionally the object-action of the functor `tdapp1_func_funcd`.             // unpack tdapp1_func_funcd at objects
rule fapp0 (@tdapp1_func_funcd $Z $E $D $FF $GG $X_Z $U_EX) $ϵ ↪ @tdapp1_fapp0_funcd $Z $E $D $FF $GG $X_Z $U_EX $ϵ;

/*
  tdapp0_func / tdapp0_fapp0 (displayed “component at (Y,V)”)

  This is the displayed analogue of `tapp0_func` / `tapp0_fapp0`.

  Usual notation (displayed categories over a base Z):
    - FF, GG : E ⟶_Z D  (displayed functors / morphisms in the slice Cat/Z),
    - ϵ : Transf_Z(FF,GG) (a displayed natural transformation),
    - choose a base object Y ∈ Obj(Z) and a fibre object V ∈ Obj(E_Y).

  Then the displayed transfor has a pointwise component in the fibre D_Y:
      ϵ_{(Y,V)} : Hom_{D_Y}( FF_Y(V), GG_Y(V) ).

  In the long-term architecture, this component should be obtained by:
    (1) forming the packaged “superscripted component” functor ϵ^(Y,V) via `tdapp1_func_funcd`,
    (2) evaluating it at the “identity” element of the source displayed representable (analogue of id_Y),
        exactly as `tapp0_fapp0` evaluates ϵ^Y at id_Y.

  Implementation status note:
    - `homd_cov` is already usable, and it has a key pointwise computation rule in the
      Grothendieck/Grothendieck case.
    - Outside that case, we have not yet committed to a full suite of computation rules / normal forms
      for the relevant displayed representables (and their “identity” base points).

  Therefore, for now we expose the displayed component as its own stable-head projection `tdapp0_fapp0`,
  packaged functorially as `tdapp0_func` (so displayed modifications act componentwise, mirroring `tapp0_func`).
*/

// For fixed (Y,V), “evaluate at (Y,V)” is functorial in ϵ (a displayed modification acts componentwise). // displayed evaluation
symbol tdapp0_func : Π [Z : Cat], Π [E D : Catd Z], Π [FF GG : τ (Obj (Functord_cat E D))],
  Π (Y_Z : τ (Obj Z)), Π (V_EY : τ (Obj (Fibre_cat E Y_Z))),
  τ (Obj (Functor_cat (Transfd_cat FF GG)
         (@Hom_cat (Fibre_cat D Y_Z)
           (@fdapp0 Z E D FF Y_Z V_EY)
           (@fdapp0 Z E D GG Y_Z V_EY))));

// Object-action of `tdapp0_func`: the pointwise displayed component ϵ_{(Y,V)}.                          // displayed component extraction
symbol tdapp0_fapp0 : Π [Z : Cat], Π [E D : Catd Z], Π [FF GG : τ (Obj (Functord_cat E D))],
  Π (Y_Z : τ (Obj Z)), Π (V_EY : τ (Obj (Fibre_cat E Y_Z))), Π (ϵ : τ (Obj (Transfd_cat FF GG))),
  τ (Obj (@Hom_cat (Fibre_cat D Y_Z)
         (@fdapp0 Z E D FF Y_Z V_EY)
         (@fdapp0 Z E D GG Y_Z V_EY)));

// β-rule: `tdapp0_fapp0` is definitionally the object-action of the functor `tdapp0_func`.              // unpack tdapp0_func at objects
rule fapp0 (@tdapp0_func $Z $E $D $FF $GG $Y_Z $V_EY) $ϵ ↪ @tdapp0_fapp0 $Z $E $D $FF $GG $Y_Z $V_EY $ϵ;

/*
  Displayed vertical identity/composition of displayed transfors, computed pointwise in fibres.

  Usual notation:
    - For ϵ : Transf_Z(FF,GG), its component at (Y,V) is a morphism in the fibre D_Y:
        ϵ_{(Y,V)} : Hom_{D_Y}( FF_Y(V), GG_Y(V) ).
    - For vertical composition η ∘ ϵ : Transf_Z(FF,HH) with ϵ : Transf_Z(FF,GG), η : Transf_Z(GG,HH),
      we have (η ∘ ϵ)_{(Y,V)} = η_{(Y,V)} ∘ ϵ_{(Y,V)} (composition in the fibre D_Y).
    - For the identity 1_FF : Transf_Z(FF,FF), we have (1_FF)_{(Y,V)} = id_{FF_Y(V)}.
*/

// Components of the identity displayed transfor compute to identity morphisms in the fibre.             // (1_FF)_{(Y,V)} ↪ id_{FF_Y(V)}
rule @tdapp0_fapp0 $Z $E $D $FF $FF $Y $V (id (Functord_cat $E $D) $FF)
  ↪ @id (Fibre_cat $D $Y) (@fdapp0 $Z $E $D $FF $Y $V);

// Components of vertical composite displayed transfors compute to vertical composition in the fibre.    // (η∘ϵ)_{(Y,V)} ↪ η_{(Y,V)} ∘ ϵ_{(Y,V)}
rule @tdapp0_fapp0 $Z $E $D $FF $HH $Y $V (@comp_fapp0 (Functord_cat $E $D) $FF $GG $HH $η $ϵ)
  ↪ @comp_fapp0 (Fibre_cat $D $Y)
      (@fdapp0 $Z $E $D $FF $Y $V)
      (@fdapp0 $Z $E $D $GG $Y $V)
      (@fdapp0 $Z $E $D $HH $Y $V)
      (@tdapp0_fapp0 $Z $E $D $GG $HH $Y $V $η)
      (@tdapp0_fapp0 $Z $E $D $FF $GG $Y $V $ϵ);

// id-instantiation (key normalization): identity displayed transfor folds to displayed action on dependent-homs.  // stable head for "ϵ = id"
//
// Usual displayed-category / slice notation (informal):
//   - Fix a base category Z.
//   - Let E,D be displayed categories over Z (objects in Cat/Z), and let FF : E ⟶_Z D be a displayed functor
//     (a morphism in the slice / a section in our “slice-style” encoding).
//   - Let 1_FF : Transf_Z(FF,FF) be the identity displayed natural transformation.
//   - Fix a fibre point (X_Z ∈ Obj(Z), U ∈ Obj(E_{X_Z})).
//     Then the “superscripted component packaging” gives a displayed functor between displayed representables:
//         (1_FF)^(X_Z,U) : Homd_E(U,−) ⟶ Homd_D(FF(U),−)
//     and this is exactly the action of FF on dependent-hom data, i.e. the stable head `fdapp1_funcd`.
//
// In emdash2 notation:
//   - `tdapp1_fapp0_funcd ... (id (Functord_cat E D) FF)` is the packaged (1_FF)^(X_Z,U),
//   - `fdapp1_funcd ... FF [X_Z] U` is the stable-head packaging of FF’s action on dependent-homs,
// so we canonically rewrite the former to the latter.
rule @tdapp1_fapp0_funcd $Z $E $D $FF $FF $X_Z $U_EX (id (Functord_cat $E $D) $FF)
  ↪ @fdapp1_funcd $Z $E $D $FF $X_Z $U_EX;

// The action of a displayed (2-)transformation on a displayed (3-)modification: fapp1_func-part of `tdapp1_func_funcd`. // displayed “components of components”
//
// Conceptual note (why this matters):
// A “displayed modification” is, by definition, a 3-cell between displayed transfors:
//   α : Hom_{Transfd_cat(FF,GG)}(ϵ,ϵ').
// Instead of introducing a separate bespoke notion of “components of modifications”, we *repackage* α
// as an ordinary (displayed) transformation between the already-packaged component functors:
//   fapp0 (tdapp1_fapp1_func ... X U ϵ ϵ') α
//     : Obj(Transfd_cat( tdapp1_fapp0_funcd ... ϵ,  tdapp1_fapp0_funcd ... ϵ')).
// Once in `Transfd_cat`, all the existing projection infrastructure applies uniformly (notably `tdapp0_fapp0`
// to extract pointwise components), so “modification” becomes “dependent transformation data” operationally.
symbol tdapp1_fapp1_func : Π [Z : Cat], Π [E D : Catd Z], Π [FF GG : τ (Obj (Functord_cat E D))],       // base+displayed cats and functors
  Π (X_Z : τ (Obj Z)) (U_EX : τ (Obj (Fibre_cat E X_Z))),                                                  // external projection index (in a fibre)
  Π [ϵ : τ (Obj (Transfd_cat FF GG))], Π [ϵ' : τ (Obj (Transfd_cat FF GG))],                                        // displayed transfors ϵ ⇒ ϵ'
  τ (Obj (Functor_cat (@Hom_cat (Transfd_cat FF GG) ϵ ϵ')                                                               // displayed modifications between ϵ and ϵ'
                 (Transfd_cat
                   (@tdapp1_fapp0_funcd Z E D FF GG X_Z U_EX ϵ)
                   (@tdapp1_fapp0_funcd Z E D FF GG X_Z U_EX ϵ'))));                             // displayed transfors between components

// β-rule: `tdapp1_fapp1_func` is definitionally the hom-action of the functor `tdapp1_func_funcd`.                // unpack tdapp1_func_funcd at homs
rule @fapp1_func _ _ (@tdapp1_func_funcd $Z $E $D $FF $GG $X_Z $U_EX) $ϵ $ϵ'
  ↪ @tdapp1_fapp1_func $Z $E $D $FF $GG $X_Z $U_EX $ϵ $ϵ';

// The action of a (2-)transformation on a (3-)modification: fapp1_func-part of `tapp1_func_funcd`.               // “components of components”
//
// Conceptual note (no new primitive notion of “modification” needed operationally):
//
// A “modification” between transfors is, by definition, a 3-cell
//   α : Hom_{Transf_cat(F,G)}(ϵ,ϵ').
// After fixing the external index X, we already have the component-packaging functors
//   ϵ^X, (ϵ')^X : Obj(Functord_cat(Hom_A(X,−), Hom_B(FX,G−))).
//
// `tapp1_fapp1_func` is precisely the functorial map that *repackages* a modification α into a
// displayed transformation between those packaged component functors:
//   fapp0 (tapp1_fapp1_func ... X ϵ ϵ') α
//     : Obj(Transfd_cat( tapp1_fapp0_funcd ... X ϵ,  tapp1_fapp0_funcd ... X ϵ')).
//
// In other words, “modification” is not treated as a standalone computational primitive here:
// it is converted into (dependent) transformation data (`Transfd_cat`), and then all existing
// operations/projections for transformations apply (notably `tdapp0_fapp0` to extract pointwise components).
symbol tapp1_fapp1_func : Π [A B : Cat], Π [F_AB G_AB : τ (Obj (Functor_cat A B))],                     // base categories and functors
  Π (X_A : τ (Obj A)),                                                                                   // external projection index
  Π [ϵ : τ (Obj (Transf_cat F_AB G_AB))], Π [ϵ' : τ (Obj (Transf_cat F_AB G_AB))],                               // transformations ϵ ⇒ ϵ'
  τ (Obj (Functor_cat (@Hom_cat (Transf_cat F_AB G_AB) ϵ ϵ')                                                          // modifications between ϵ and ϵ'
                 (Transfd_cat
                   (@tapp1_fapp0_funcd A B F_AB G_AB X_A ϵ)
                   (@tapp1_fapp0_funcd A B F_AB G_AB X_A ϵ'))));                                      // dependent transf between components

// β-rule: `tapp1_fapp1_func` is definitionally the hom-action of the functor `tapp1_func_funcd`.                  // unpack tapp1_func_funcd at homs
rule @fapp1_func _ _ (@tapp1_func_funcd $A $B $F_AB $G_AB $X_A) $ϵ $ϵ'
  ↪ @tapp1_fapp1_func $A $B $F_AB $G_AB $X_A $ϵ $ϵ';


// -------------------------------------------------------------------------------------------------
// 17. Sanity checks (lightweight “unit tests” for rewrite normalization)                             // keep small, avoids proof noise
// -------------------------------------------------------------------------------------------------

// Op_cat involution reduces by rewriting.                                                            // checks Op_cat rule fires
assert ⊢ Op_cat (Op_cat Cat_cat) ≡ Cat_cat;                                                          // (Cat_catᵒᵖ)ᵒᵖ ≡ Cat_cat

// Identity functor on objects reduces by rewriting.                                                  // checks fapp0(id_func) β-rule
compute fapp0 (@id Cat_cat Terminal_cat) Terminal_obj;                                    // normal form should be `Terminal_obj`

// tapp1_func_funcd object-action reduces to tapp1_fapp0_funcd by rewriting.                                         // checks tapp β-rule fires
assert [A B : Cat] [F_AB G_AB : τ (Obj (Functor_cat A B))] (X_A : τ (Obj A)) (ϵ : τ (Obj (Transf_cat F_AB G_AB))) ⊢
  fapp0 (@tapp1_func_funcd A B F_AB G_AB X_A) ϵ ≡ @tapp1_fapp0_funcd A B F_AB G_AB X_A ϵ;

// id-instantiation: tapp1_fapp0_funcd at identity transfor folds to the stable head fapp1_funcd.                  // checks tapp-id fold fires
assert [A B : Cat] (F : τ (Obj (Functor_cat A B))) (X_A : τ (Obj A)) ⊢
  @tapp1_fapp0_funcd A B F F X_A (id (Functor_cat A B) F) ≡ @fapp1_funcd A B F X_A;

// id-instantiation (packaged view): specialization of tapp1_func_funcd at identity transfor folds to fapp1_funcd. // checks packaged-id fold fires
assert [A B : Cat] (F : τ (Obj (Functor_cat A B))) (X_A : τ (Obj A)) ⊢
  fapp0 (@tapp1_func_funcd A B F F X_A) (id (Functor_cat A B) F) ≡ @fapp1_funcd A B F X_A;

// tapp0_fapp0 is the derived “component at Y” (evaluation at id_Y) and reduces by rewriting.          // checks tapp0 β-rule fires
assert [A B : Cat] [F_AB G_AB : τ (Obj (Functor_cat A B))] (Y_A : τ (Obj A)) (ϵ : τ (Obj (Transf_cat F_AB G_AB))) ⊢
  fapp0 (@tapp0_func A B F_AB G_AB Y_A) ϵ ≡ @tapp0_fapp0 A B F_AB G_AB Y_A ϵ;

// id/comp in Functor_cat compute pointwise via tapp0_fapp0.                                            // checks vertical laws for components
assert [A B : Cat] (F : τ (Obj (Functor_cat A B))) (Y : τ (Obj A)) ⊢
  @tapp0_fapp0 A B F F Y (id (Functor_cat A B) F) ≡ @id B (@fapp0 A B F Y);

assert [A B : Cat] (F G H : τ (Obj (Functor_cat A B))) (Y : τ (Obj A))
  (ϵ : τ (Obj (Transf_cat F G))) (η : τ (Obj (Transf_cat G H))) ⊢
  @tapp0_fapp0 A B F H Y (@comp_fapp0 (Functor_cat A B) F G H η ϵ)
    ≡ @comp_fapp0 B
        (@fapp0 A B F Y)
        (@fapp0 A B G Y)
        (@fapp0 A B H Y)
        (@tapp0_fapp0 A B G H Y η)
        (@tapp0_fapp0 A B F G Y ϵ);

// tdapp1_func_funcd object-action reduces to tdapp1_fapp0_funcd by rewriting.                                       // checks tdapp β-rule fires
assert [Z : Cat] [E D : Catd Z] [FF GG : τ (Obj (Functord_cat E D))]
  (X_Z : τ (Obj Z)) (U_EX : τ (Obj (Fibre_cat E X_Z))) (ϵ : τ (Obj (Transfd_cat FF GG))) ⊢
  fapp0 (@tdapp1_func_funcd Z E D FF GG X_Z U_EX) ϵ ≡ @tdapp1_fapp0_funcd Z E D FF GG X_Z U_EX ϵ;

// id-instantiation: tdapp1_fapp0_funcd at identity displayed transfor folds to the stable head fdapp1_funcd.      // checks tdapp-id fold fires
assert [Z : Cat] [E D : Catd Z] (FF : τ (Obj (Functord_cat E D)))
  (X_Z : τ (Obj Z)) (U_EX : τ (Obj (Fibre_cat E X_Z))) ⊢
  @tdapp1_fapp0_funcd Z E D FF FF X_Z U_EX (id (Functord_cat E D) FF) ≡ @fdapp1_funcd Z E D FF X_Z U_EX;

// id-instantiation (packaged view): specialization of tdapp1_func_funcd at identity displayed transfor folds.     // checks packaged-id fold fires
assert [Z : Cat] [E D : Catd Z] (FF : τ (Obj (Functord_cat E D)))
  (X_Z : τ (Obj Z)) (U_EX : τ (Obj (Fibre_cat E X_Z))) ⊢
  fapp0 (@tdapp1_func_funcd Z E D FF FF X_Z U_EX) (id (Functord_cat E D) FF) ≡ @fdapp1_funcd Z E D FF X_Z U_EX;

// tdapp0_fapp0 is the displayed “component at (Y,V)” and is the object-action of tdapp0_func.                  // checks tdapp0 β-rule fires
assert [Z : Cat] [E D : Catd Z] [FF GG : τ (Obj (Functord_cat E D))]
  (Y_Z : τ (Obj Z)) (V_EY : τ (Obj (Fibre_cat E Y_Z))) (ϵ : τ (Obj (Transfd_cat FF GG))) ⊢
  fapp0 (@tdapp0_func Z E D FF GG Y_Z V_EY) ϵ ≡ @tdapp0_fapp0 Z E D FF GG Y_Z V_EY ϵ;

// id/comp in Functord_cat compute pointwise in fibres via tdapp0_fapp0.                               // checks vertical laws for displayed components
assert [Z : Cat] [E D : Catd Z] (FF : τ (Obj (Functord_cat E D)))
  (Y : τ (Obj Z)) (V : τ (Obj (Fibre_cat E Y))) ⊢
  @tdapp0_fapp0 Z E D FF FF Y V (id (Functord_cat E D) FF)
    ≡ @id (Fibre_cat D Y) (@fdapp0 Z E D FF Y V);

assert [Z : Cat] [E D : Catd Z] (FF GG HH : τ (Obj (Functord_cat E D)))
  (Y : τ (Obj Z)) (V : τ (Obj (Fibre_cat E Y)))
  (ϵ : τ (Obj (Transfd_cat FF GG))) (η : τ (Obj (Transfd_cat GG HH))) ⊢
  @tdapp0_fapp0 Z E D FF HH Y V (@comp_fapp0 (Functord_cat E D) FF GG HH η ϵ)
    ≡ @comp_fapp0 (Fibre_cat D Y)
        (@fdapp0 Z E D FF Y V)
        (@fdapp0 Z E D GG Y V)
        (@fdapp0 Z E D HH Y V)
        (@tdapp0_fapp0 Z E D GG HH Y V η)
        (@tdapp0_fapp0 Z E D FF GG Y V ϵ);

// tapp1_func_funcd hom-action reduces to tapp1_fapp1_func by rewriting (uses @Hom_cat(Functord_cat..) ≡ Transfd_cat).        // checks tapp fapp1_func β-rule fires
assert [A B : Cat] [F_AB G_AB : τ (Obj (Functor_cat A B))] (X_A : τ (Obj A))
  (ϵ : τ (Obj (Transf_cat F_AB G_AB))) (ϵ' : τ (Obj (Transf_cat F_AB G_AB))) ⊢
  @fapp1_func _ _ (@tapp1_func_funcd A B F_AB G_AB X_A) ϵ ϵ' ≡ @tapp1_fapp1_func A B F_AB G_AB X_A ϵ ϵ';

// tdapp1_func_funcd hom-action reduces to tdapp1_fapp1_func by rewriting.                                         // checks tdapp fapp1_func β-rule fires
assert [Z : Cat] [E D : Catd Z] [FF GG : τ (Obj (Functord_cat E D))]
  (X_Z : τ (Obj Z)) (U_EX : τ (Obj (Fibre_cat E X_Z)))
  (ϵ : τ (Obj (Transfd_cat FF GG))) (ϵ' : τ (Obj (Transfd_cat FF GG))) ⊢
  @fapp1_func _ _ (@tdapp1_func_funcd Z E D FF GG X_Z U_EX) ϵ ϵ' ≡ @tdapp1_fapp1_func Z E D FF GG X_Z U_EX ϵ ϵ';

// Pullback of a Grothendieck isofibration reduces to Grothendieck of precomposition.                 // checks Pullback_catd/∫ rewrite fires
assert [A B : Cat] (E : τ (Obj (Functor_cat B Cat_cat))) (F : τ (Obj (Functor_cat A B))) ⊢
  @Pullback_catd A B (@Fibration_cov_catd B E) F
    ≡ @Fibration_cov_catd A (@comp_fapp0 Cat_cat A B Cat_cat E F);

// Casting Cat to Catd(1) behaves as expected.                                                        // checks Lift_catd/Lift_funcd rules fire
assert [A : Cat] ⊢ Total_cat (Lift_catd A) ≡ A;
assert [A : Cat] (x1 : τ (Obj Terminal_cat)) ⊢ Fibre_cat (Lift_catd A) x1 ≡ A;
assert [A B : Cat] (F : τ (Obj (Functor_cat A B))) ⊢ Unlift_func (Lift_funcd F) ≡ F;
assert [A B : Cat] (F : τ (Obj (Functor_cat A B))) (x1 : τ (Obj Terminal_cat)) (x : τ (Obj A)) ⊢
  @fdapp0 Terminal_cat (Lift_catd A) (Lift_catd B) (@Lift_funcd A B F) x1 x ≡ @fapp0 A B F x;
