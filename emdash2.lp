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
// 1. Equality / path groupoid (Id-type valued in `Grpd`)                                           // HoTT-style equality
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

// -------------------------------------------------------------------------------------------------
// 3. Natural numbers (used as a dimension/index type in drafts)                                     // globular/simplicial indices
// -------------------------------------------------------------------------------------------------

inductive Nat : TYPE ≔                                                                              // Peano naturals as an index object
| Z : Nat                                                                                           // zero (dimension 0)
| S : Nat → Nat;                                                                                    // successor (dimension n+1)

// -------------------------------------------------------------------------------------------------
// 4. Categories as a classifier `Cat : TYPE` with `Obj : Cat → Grpd` and `Hom_cat : ... → Cat`          // strict ω-category skeleton
// -------------------------------------------------------------------------------------------------

constant symbol Cat : TYPE;                                                                         // classifier of (strict/lax) ω-categories

// Objects of a category form a groupoid (`Grpd`), not just a set.                                   // higher-categorical “objects up to paths”
injective symbol Obj : Cat → Grpd;                                                                  // object classifier of a category

// Hom_cat is itself a category: for X,Y : Obj(A), Hom_A(X,Y) : Cat.                                     // hom-categories (enriched/globular view)
injective symbol Hom_cat : Π [A : Cat] (X_A Y_A : τ (Obj A)), Cat;                            // hom-category as a Cat

// Identity morphism: an object in the hom-category Hom_A(X,X).                                      // identity 1-cell (and higher units implicitly)
injective symbol identity_morph : Π (A : Cat), Π (X_A: τ (Obj A)), τ (Obj (Hom_cat X_A X_A));            // id_X : Obj(Hom_cat(X,X))

// -------------------------------------------------------------------------------------------------
// 4b. Opposite category (core)                                                                      // A ↦ Aᵒᵖ (objects fixed, arrows reversed)
// -------------------------------------------------------------------------------------------------

injective symbol Op_cat : Cat → Cat;                                                                 // opposite category operation
rule Op_cat (Op_cat $A) ↪ $A;                                                                        // involutive law: (Aᵒᵖ)ᵒᵖ ≡ A

// Objects are unchanged by opposite.                                                                // Obj(Aᵒᵖ) ≡ Obj(A)
rule Obj (Op_cat $A) ↪ Obj $A;

// Homs are reversed by opposite.                                                                    // Hom_{Aᵒᵖ}(X,Y) ≡ Hom_A(Y,X)
rule @Hom_cat (Op_cat $A) $X $Y ↪ @Hom_cat $A $Y $X;

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
  Π (g: τ (Obj (Hom_cat Y_A Z_A))), Π (f: τ (Obj (Hom_cat X_A Y_A))),                                        // composable morphisms g ∘ f
  τ (Obj (Hom_cat X_A Z_A));                                                                             // composite morphism in Hom_cat(X,Z)

// -------------------------------------------------------------------------------------------------
// 5. Functors (as objects of a functor-category `Functor_cat A B : Cat`)                                // ω-functors
// -------------------------------------------------------------------------------------------------

// The “functor category” between A and B (objects are functors, morphisms are transformations).     // internal functor category
constant symbol Functor_cat : Π (A B : Cat), Cat;                                            // Functor_cat(A,B) : Cat

// Action of a functor on objects.                                                                   // F₀ : Obj(A) → Obj(B)
symbol fapp0 : Π [A B : Cat], Π (F_AB : τ (Obj (Functor_cat A B))),                            // functor object F ∈ Obj(Functor_cat(A,B))
  τ (Obj A) → τ (Obj B);                                                                            // send X_A ↦ F_AB(X_A)

// Action of a functor on hom-categories: gives a functor Hom_A(X,Y) → Hom_B(FX,FY).                 // F₁ as a functor (ω-level)
symbol fapp1_func : Π [A B : Cat], Π (F_AB : τ (Obj (Functor_cat A B))),                            // functor object F
  Π [X_A Y_A : τ (Obj A)],                                                            // endpoints
  τ (Obj (Functor_cat (Hom_cat X_A Y_A) (Hom_cat (fapp0 F_AB X_A) (fapp0 F_AB Y_A))));                            // functor on the hom-category

// Opposite of a functor: F : A→B  ↦  Fᵒᵖ : Aᵒᵖ → Bᵒᵖ (same object-map, reversed hom-action).        // dualization of functors
injective symbol Op_func : Π [A B : Cat],
  τ (Obj (Functor_cat A B)) → τ (Obj (Functor_cat (Op_cat A) (Op_cat B)));

// Involution: (Fᵒᵖ)ᵒᵖ ≡ F (definitionally, up to Op_cat involution).                                 // (−)ᵒᵖ is involutive
rule Op_func (@Op_func $A $B $F) ↪ $F;

// Object-action is unchanged by opposite.                                                            // Fᵒᵖ₀ = F₀
rule @fapp0 (Op_cat $A) (Op_cat $B) (@Op_func $A $B $F) $xA ↪ @fapp0 $A $B $F $xA;

// Hom-action is reversed by opposite (uses definitional Hom_{Aᵒᵖ}(X,Y) ≡ Hom_A(Y,X)).                // Fᵒᵖ₁(X,Y) = F₁(Y,X)
rule @fapp1_func (Op_cat $A) (Op_cat $B) (@Op_func $A $B $F) $X $Y
  ↪ @fapp1_func $A $B $F $Y $X;

// -------------------------------------------------------------------------------------------------
// 6. Classifier categories: `Grpd_cat` and `Cat_cat` (categories of groupoids and categories)       // “universes as categories”
// -------------------------------------------------------------------------------------------------

// `Grpd_cat` plays the role of the category of groupoids/sets (discrete fibrations classifier).     // analogue of Set/Type-as-a-category
constant symbol Grpd_cat : Cat;                                                                     // category of ∞-groupoids
unif_rule τ (Obj $A) ≡ Grpd ↪ [ $A ≡ Grpd_cat ];                                                     // infer A ≡ Grpd_cat when Obj(A) decodes to Grpd
rule τ (Obj (@Hom_cat Grpd_cat $X $Y)) ↪ (τ $X → τ $Y);                                                  // morphisms in Grpd_cat are functions

// `Cat_cat` is the category of categories (fibrations classifier).                                  // Cat of categories
constant symbol Cat_cat : Cat;                                                                      // category of categories
unif_rule τ (Obj $A) ≡ Cat ↪ [ $A ≡ Cat_cat ];                                                       // infer A ≡ Cat_cat when Obj(A) decodes to Cat
rule @Hom_cat Cat_cat $X $Y ↪ Functor_cat $X $Y;                                                            // morphisms in Cat_cat are functors

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
rule @fapp0 Cat_cat Cat_cat op $A ↪ Op_cat $A;

// Morphism-action on objects (functors): op₁(F) ≡ Fᵒᵖ.                                               // fapp0(fapp1_func(op),F) ↪ Op_func(F)
rule @fapp0 (Functor_cat $A1 $A2) (Functor_cat (Op_cat $A1) (Op_cat $A2))
  (@fapp1_func Cat_cat Cat_cat op $A1 $A2) $F ↪ @Op_func $A1 $A2 $F;

// Identity functor on a category A (as an object in Functor_cat(A,A)).                                  // 1-category identity, lifted to ω setting
symbol Id_func [A: Cat] : τ (Obj (Functor_cat A A))                                             // identity functor id_A : Obj(Functor_cat(A,A))
≔ @identity_morph Cat_cat A;                                                                        // defined as identity morphism in Cat_cat
// NOTE: `Id_func` is currently a definitional abbreviation; if we ever need rewrite rules with head `Id_func`, switch to `symbol Id_func ...;` + `rule Id_func ... ↪ ...` (cf. tapp0_fapp0).
rule fapp0 (@identity_morph Cat_cat $A) $xA ↪ $xA;                                                   // computation: (id_A)(x) ↪ x

// Opposite of identity is identity.                                                                  // (id_A)ᵒᵖ ≡ id_{Aᵒᵖ}
rule @Op_func $A $A (@Id_func $A) ↪ @Id_func (Op_cat $A);

// Opposite respects composition of functors (in Cat_cat).                                            // (F∘G)ᵒᵖ ≡ Fᵒᵖ∘Gᵒᵖ
rule @Op_func $A1 $A3 (@comp_fapp0 Cat_cat $A1 $A2 $A3 $F $G)
  ↪ @comp_fapp0 Cat_cat (Op_cat $A1) (Op_cat $A2) (Op_cat $A3) (@Op_func $A2 $A3 $F) (@Op_func $A1 $A2 $G);

// Covariant “hom functor” / Yoneda-style precomposition: Hom_A(W, F(-)).                             // hom-covariant / representable functor core
constant symbol hom_cov : Π [A : Cat], Π (W_A: τ (Obj A)), Π [B : Cat],                               // W_A ∈ Obj(A), F : Functor_cat(B,A)
  Π (F_BA : τ (Obj (Functor_cat B A))), τ (Obj (Functor_cat B Cat_cat));                                     // result: B → Cat_cat (a Cat-valued functor)
rule fapp0 (hom_cov $X $F) $Y ↪ Hom_cat $X (fapp0 $F $Y);                                                // object action: Y ↦ Hom_A(X, F(Y))

// Computation (hom_cov acts by postcomposition):                                                      // ((Hom_A(W,F-))_1 f)_0 g ↪ (Ff)∘g
// If f : Hom_B(X,Y) and g : Hom_A(W,F(X)), then `hom_cov W F : B → Cat` induces a functor
//   Hom_A(W,F(X)) → Hom_A(W,F(Y))
// which sends g ↦ (F f) ∘ g.
//
// Key point: keep *multiple* inferred arguments on the LHS underspecified (`_`) to avoid conversion blowups,
// especially when an implicit argument would contain reducible subterms like `fapp0 $F $X`.
rule @fapp0 _
    _
    (@fapp0 (Hom_cat $X $Y)
      _
      (@fapp1_func $B Cat_cat (@hom_cov $A $W $B $F) $X $Y) $f) $g
  ↪ @comp_fapp0 $A $W (fapp0 $F $X) (fapp0 $F $Y)
      (@fapp0 (Hom_cat $X $Y)
        _
        (@fapp1_func $B $A $F $X $Y) $f) $g;

// Postcomposition by op computes pointwise: (op ∘ E)(b) ≡ (E(b))ᵒᵖ.                                   // key for “twisted” fibrations
rule @fapp0 $B Cat_cat (@comp_fapp0 Cat_cat $B Cat_cat Cat_cat op $E) $b
  ↪ Op_cat (@fapp0 $B Cat_cat $E $b);

// Naturality w.r.t. precomposition in the argument functor: Hom_A(W, F(-)) ∘ G  ≡  Hom_A(W, (F∘G)(-)). // "accumulate the functor"
// Note: we express functor composition via `comp_fapp0` in `Cat_cat` (not via `compFunc`, which is defined later). // computational-friendly
rule @comp_fapp0 Cat_cat $C $B Cat_cat (@hom_cov $A $W $B $F) $G
  ↪ @hom_cov $A $W $C (@comp_fapp0 Cat_cat $C $B $A $F $G);

// Sanity: the above rewrite fires definitionally (conversion).                                        // exercise the rule
assert [A B : Cat] [C : Cat] (W : τ (Obj A))
  (F : τ (Obj (Functor_cat B A))) (G : τ (Obj (Functor_cat C B))) ⊢
  @comp_fapp0 Cat_cat C B Cat_cat (@hom_cov A W B F) G
    ≡ @hom_cov A W C (@comp_fapp0 Cat_cat C B A F G);

// Sanity: postcomposition by op normalizes pointwise.                                                // exercise `op ∘ E` computation
assert [B : Cat] (E : τ (Obj (Functor_cat B Cat_cat))) (b : τ (Obj B)) ⊢
  @fapp0 B Cat_cat (@comp_fapp0 Cat_cat B Cat_cat Cat_cat op E) b
    ≡ Op_cat (@fapp0 B Cat_cat E b);

// Sanity: opposite distributes over functor composition in Cat_cat.                                  // (F∘G)ᵒᵖ = Fᵒᵖ∘Gᵒᵖ
assert [A B C : Cat] (F : τ (Obj (Functor_cat B C))) (G : τ (Obj (Functor_cat A B))) ⊢
  @Op_func A C (@comp_fapp0 Cat_cat A B C F G)
    ≡ @comp_fapp0 Cat_cat (Op_cat A) (Op_cat B) (Op_cat C) (@Op_func B C F) (@Op_func A B G);

// Sanity: general hom_cov action computes to postcomposition by F(f).                                 // ((hom_cov W F)_1 f)_0 g ↪ (Ff)∘g
assert [A B : Cat] (W : τ (Obj A)) (F : τ (Obj (Functor_cat B A)))
  (X Y : τ (Obj B)) (f : τ (Obj (Hom_cat X Y))) (g : τ (Obj (Hom_cat W (fapp0 F X)))) ⊢
  @fapp0 (Hom_cat W (fapp0 F X)) (Hom_cat W (fapp0 F Y))
    (@fapp0 (Hom_cat X Y)
      (Functor_cat (Hom_cat W (fapp0 F X)) (Hom_cat W (fapp0 F Y)))
      (@fapp1_func B Cat_cat (@hom_cov A W B F) X Y) f) g
    ≡ @comp_fapp0 A W (fapp0 F X) (fapp0 F Y)
        (@fapp0 (Hom_cat X Y) (Hom_cat (fapp0 F X) (fapp0 F Y))
          (@fapp1_func B A F X Y) f) g;

// Internalized (bifunctorial) covariant hom: for fixed F:B→A, we get a functor Aᵒᵖ → (B → Cat).    // Hom_A(-,F(-)) as a functor
// In ordinary notation: hom_cov_func(F) : A^op ⇒ Functor_cat(B,Cat_cat), i.e. A^op ⇒ B ⇒ Cat.
constant symbol hom_cov_func : Π [A : Cat], Π [B : Cat],
  Π (F_BA : τ (Obj (Functor_cat B A))), τ (Obj (Functor_cat (Op_cat A) (Functor_cat B Cat_cat)));

// β-rule for object-action: at X : Obj(Aᵒᵖ) (i.e. X : Obj(A)), hom_cov_func(F)(X) ≡ hom_cov(X,F).   // fapp0(hom_cov_func(F),X) ↪ hom_cov(X,F)
rule fapp0 (@hom_cov_func $A $B $F) $X ↪ @hom_cov $A $X $B $F;

// Sanity: the β-rule fires, and the resulting functor still computes pointwise via hom_cov.         // exercise both rewrites
assert [A B : Cat] (F : τ (Obj (Functor_cat B A))) (X : τ (Obj (Op_cat A))) ⊢
  fapp0 (hom_cov_func F) X ≡ @hom_cov A X B F;

assert [A B : Cat] (F : τ (Obj (Functor_cat B A))) (X : τ (Obj (Op_cat A))) (Y : τ (Obj B)) ⊢
  fapp0 (fapp0 (hom_cov_func F) X) Y ≡ @Hom_cat A X (fapp0 F Y);


// -------------------------------------------------------------------------------------------------
// 7. Dependent categories (displayed categories over a base)                                        // Cat-valued type families
// -------------------------------------------------------------------------------------------------

// `Catd B` is the type of displayed categories over `B` in the “category over a base” sense.          // Cat/B objects
// Usual notation/terminology: an element `E : Catd B` should be thought of as a functor `p : E ⟶ B`
// (a category equipped with a projection to `B`), possibly with extra structure later (e.g. isofibration,
// opfibration, cartesian lifts).                                                                      // p : E → B
constant symbol Catd : Π (A : Cat), TYPE;                                                           // classifier of dependent categories over A

/*
  Visualization: (iso)fibrations as “simplicial” shapes (edges / surfaces / volumes / …)

  A helpful mental model in this development is to think of a (covariant) (iso)fibration `E → B` as
  a classifier of “arrows in B”, i.e. *edges*.

  Prototypical example (representable / co-slice codomain fibration):
  - Given `X_B : Obj(B)`, the representable functor `Hom_B(X_B,-)` is (in our notations) `hom_cov X_B`,
    or explicitly `hom_cov X_B (@Id_func B) : Obj(Functor_cat B Cat_cat)`.
  - Its Grothendieck construction `IsoFibration_catd (hom_cov X_B (@Id_func B)) : Catd B`
    has fibre at `Y_B : Obj(B)` equal to `Hom_B(X_B,Y_B)` (by the rewrite rule for `Fibre_cat`).
    So an “element” over `Y_B` can be visualized as an arrow `X_B → Y_B` (an *edge*).

  Iteration suggests higher simplices:
  - A fibration `S → E` (i.e. a displayed category over `Total_cat E`) can be visualized as classifying
    “2-arrows”, i.e. *surfaces*. In our notations this is approximated by `homd_cov`.
    Notice in the type of `homd_cov` the base product
      `Product_catd B (IsoFibration_catd (hom_cov W_Z (@Id_func Z)))`,
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
// We keep the historical name `IsoFibration_catd` for now; we can rename once the (op)fibration interface is stabilized.
constant symbol IsoFibration_catd : Π [A : Cat], τ (Obj (Functor_cat A Cat_cat)) → Catd A;               // ∫M : Catd(A) for M : A → Cat

/*
  Displayed/dependent functors: slice-style vs general base functor

  - In cartierSolution13.lp, a displayed functor can be "over an arbitrary base functor":
      funcd A F B   (A : catd X, B : catd Y, F : func X Y)
    so a displayed morphism remembers a base map F : X → Y.
    Composition then produces a displayed functor over the composite base map (F∘G).

  - In emdash2.lp we choose the *slice-style* presentation:
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
      Pullback_catd (IsoFibration_catd E) F  ↪  IsoFibration_catd (E ∘ F).
*/

// `Functord_cat E D` is the category of functors over a fixed base `B`.                                 // Fun_B(E,D) / hom in Cat/B
// Usual notation: if `p:E⟶B` and `q:D⟶B`, then an object of `Functord_cat(E,D)` is a functor `F:E⟶D`
// such that `q ∘ F = p` (i.e. a morphism in the slice category `Cat/B`).                               // commuting triangle
constant symbol Functord_cat : Π [B : Cat], Π (E D : Catd B), Cat;                          // Functord_cat(E,D) : Cat

// Dependent identity functor (identity section).                                                    // id in the slice category
constant symbol Id_funcd [B : Cat] [E:Catd B] : τ (Obj (Functord_cat E E));                      // id : Obj(Functord_cat(E,E))

// Dependent composition of dependent functors.                                                      // composition in the slice Cat/B
symbol comp_funcd [B : Cat] [E D : Catd B] [C:Catd B]                                   // base B and displayed categories E,D,C
  (FF: τ (Obj (Functord_cat D C))) (GG: τ (Obj (Functord_cat E D))) : τ (Obj (Functord_cat E C));               // compose : (D→C) × (E→D) → (E→C)

// Fibre of a dependent category E over X_B : Obj(B) (displayed category at a base object).          // E[X_B] in type theory
injective symbol Fibre_cat : Π [B : Cat] (E : Catd B) (X_B : τ (Obj B)), Cat;                          // fibre category at X_B

// Fibre of a Grothendieck construction is the original value (strictly, on objects).                // ∫M fibre at x is M(x)
rule Fibre_cat (IsoFibration_catd $M) $x ↪ fapp0 $M $x;                                              // fibre(∫M,x) ↪ M(x)

// Sanity (derived instance): representable fibration.                                                 // fibre(∫Hom(X,F-),x) ≡ Hom(X,Fx)
// This is not an extra computation rule: it follows by rewriting with the general Grothendieck fibre
// rule above and the `hom_cov` object-action rule `fapp0 (hom_cov X F) x ↪ Hom_cat X (fapp0 F x)`.
assert [B A : Cat] (X_A : τ (Obj A)) (F : τ (Obj (Functor_cat B A))) (x : τ (Obj B)) ⊢
  Fibre_cat (IsoFibration_catd (hom_cov X_A F)) x ≡ Hom_cat X_A (fapp0 F x);

// Pullback of a dependent category along a functor (reindexing/substitution).                       // substitution / base change
symbol Pullback_catd : Π [A B : Cat], Catd B → τ (Obj (Functor_cat A B)) → Catd A;               // F^*(E) : Catd(A)
rule Fibre_cat (Pullback_catd $E $F) $xA ↪ Fibre_cat $E (fapp0 $F $xA);                              // fibre(F^*E,x) ↪ fibre(E,Fx)

// Pullback of an isofibration (Grothendieck construction) is isofibration of the precomposition.    // ∫(E∘F) ≅ F^*(∫E)
// Here `E : B → Cat_cat` and `F : A → B`, and we express `E∘F` via composition in `Cat_cat`.         // avoids relying on later `compFunc`
// This is the key bridge for “general base functor” displayed maps: reindex first, then use Functord_cat. // simulate funcd-over-F
rule @Pullback_catd $A $B (@IsoFibration_catd $B $E) $F
  ↪ @IsoFibration_catd $A (@comp_fapp0 Cat_cat $A $B Cat_cat $E $F);

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
*/
symbol tapp1_func_funcd : Π [A B : Cat], Π [F_AB G_AB : τ (Obj (Functor_cat A B))],                      // domain/codomain categories and functors
  Π (X_A: τ (Obj A)),                                                                                   // external/superscript projection index
  τ (Obj (Functor_cat (Transf_cat F_AB G_AB)
         (Functord_cat (IsoFibration_catd (hom_cov X_A (@Id_func A)))                             // source: Hom_A(X_A,-) over A
                  (IsoFibration_catd (hom_cov (fapp0 F_AB X_A) G_AB)))));                               // target: Hom_B(FX_A, G_AB(-)) over A

// `tapp1_fapp0_funcd` is the fapp0 part of `tapp1_func_funcd`
symbol tapp1_fapp0_funcd : Π [A B : Cat], Π [F_AB G_AB : τ (Obj (Functor_cat A B))],                      // domain/codomain categories and functors
  Π (X_A: τ (Obj A)), Π (ϵ : τ (Obj (Transf_cat F_AB G_AB))),                                              // ϵ : Obj(Transf_cat(F,G))
  τ (Obj (Functord_cat (IsoFibration_catd (hom_cov X_A (@Id_func A)))                             // source: Hom_A(X_A,-)
                  (IsoFibration_catd (hom_cov (fapp0 F_AB X_A) G_AB))));                                // target: Hom_B(FX_A, G_AB(-))

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
injective symbol Total_proj_func [B : Cat] (E: Catd B) : τ (Obj (Functor_cat (Total_cat E) B));           // functor object in Functor_cat(∫E, B)

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
  “transport on objects” operation `isoFib_transport0` and give it strict functoriality rules on
  objects (preservation of identities and composition).

  This is intentionally strict for now (non-lax), as requested; later we can relax it by replacing
  these rules with higher-cell data (laxity 2-cells).
*/

// Transport objects in the fibre along a base 1-cell (covariant).                                    // M(f) on objects
// Usual notation: `f_!(u)` or `M(f)(u)` (opfibration / covariant transport on objects).               // f_! : M(x) → M(y) (on objects)
sequential symbol isoFib_transport0 : Π [B : Cat] (M : τ (Obj (Functor_cat B Cat_cat))),
  Π [x y : τ (Obj B)], Π (f : τ (Obj (Hom_cat x y))), Π (u : τ (Obj (fapp0 M x))),
  τ (Obj (fapp0 M y));

// Canonicalization: compute (M(f))(u) *towards* `isoFib_transport0 M f u`.                             // fold transport0
// Usual notation: `M(f)(u) ↦ f_!(u)`.                                                                 // fold to the transport head
// This keeps `isoFib_transport0` as the stable head symbol (like `comp_fapp0`), so later
// object-level functoriality rules apply without unfolding.
rule fapp0 (fapp0 (@fapp1_func $B Cat_cat $M $x $y) $f) $u
  ↪ @isoFib_transport0 $B $M $x $y $f $u;

// Strict functoriality on objects: M(id)(u) ↪ u.                                                      // preserves identities on objects
// Usual notation: `(id_x)_!(u) = u`.                                                                  // id_! = id
rule @isoFib_transport0 $B $M $x $x (identity_morph $B $x) $u ↪ $u;

// Strict functoriality on objects: M(g∘f)(u) ↪ M(g)(M(f)(u)).                                         // preserves composition on objects
// Usual notation: `(g ∘ f)_!(u) = g_!(f_!(u))`.                                                       // (g∘f)_! = g_!∘f_! (on objects)
rule @isoFib_transport0 $B $M $x $z (@comp_fapp0 $B $x $y $z $g $f) $u
  ↪ @isoFib_transport0 $B $M $y $z $g (@isoFib_transport0 $B $M $x $y $f $u);

// Dependent projection π₂ as a dependent functor into the pulled-back family over ∫M.               // second projection (displayed)
injective symbol Total_proj_funcd [B : Cat] (E: Catd B) :                                             // dependent object: section over ∫E
  τ (Obj (Functord_cat (Terminal_catd (Total_cat E)) (Pullback_catd E (Total_proj_func E))));            // π₂ : 1_{∫E} ⇒ (π₁)^*E

injective symbol Total_intro_func : Π [B : Cat] [E D : Catd B],
τ (Obj (Functord_cat E D)) → τ (Obj (Functor_cat (Total_cat E) (Total_cat D)));

// Terminal displayed functor into the terminal family (slice-style).                                 // unique map A → 1_X in Catd(X)
injective symbol Terminal_funcd : Π [B : Cat] (E : Catd B), τ (Obj (Functord_cat E (Terminal_catd B)));

// Terminal comprehension laws (cartierSolution13: Context_cat/Context_elimCat/Context_intro).        // ∫(1_X) ≡ X, π₁ ≡ id
rule Total_cat (Terminal_catd $A) ↪ $A;                                                               // ∫(1_A) ↪ A
rule Total_proj_func (Terminal_catd $A) ↪ @Id_func $A;                                        // π₁ : ∫(1_A)→A ↪ id_A

// Pullback preserves terminal displayed categories.                                                  // F^*(1_B) ≡ 1_A
rule @Pullback_catd $A $B (Terminal_catd $B) $F ↪ Terminal_catd $A;

// The dependent projection π₂ is the identity section when M is terminal.                            // π₂ : 1_{∫1} ⇒ (π₁)^*1  ↪ id
rule Total_proj_funcd (Terminal_catd $A) ↪ @Id_funcd $A (Terminal_catd $A);

// Intro rules: functor between totals induced by a displayed functor in the slice.                   // Context_intro_func analogues
rule @Total_intro_func $X $A $A (@Id_funcd $X $A) ↪ @Id_func (Total_cat $A);     // ∫id ↪ id
rule @Total_intro_func $X $A (Terminal_catd $X) (Terminal_funcd $A) ↪ Total_proj_func $A;        // ∫(!) ↪ π₁

// β-like law: composing the induced functor with the projection of B gives the projection of A.      // (∫FF);π₁_B = π₁_A
rule @comp_fapp0 Cat_cat (Total_cat $A) (Total_cat $B) $X (Total_proj_func $B) (@Total_intro_func $X $A $B $FF)
  ↪ Total_proj_func $A;

// TODO: Review this claim: such additional rewrite rules are for convenience:
// Objects of ∫M are Σ (x : Obj(B)), Obj(M(x)), but **only** for Grothendieck totals.                 // Σ-object description (Grothendieck only)
// For a general `E : Catd B` (semantic “category over B”), objects of `Total_cat E` are not
// definitionally a Σ-type: `Total_cat` is primitive data carried by `E`.
rule τ (Obj (Total_cat (@IsoFibration_catd $B $M)))
  ↪ `τΣ_ x : τ (Obj $B), Obj (fapp0 $M x);                                                            // τ Obj(∫M) ↪ Σ x:B, Obj(M(x))

// The base projection π₁ : ∫M → B sends (x,u) ↦ x.                                                    // compute π₁ on objects (Grothendieck)
rule fapp0 (Total_proj_func (IsoFibration_catd $M)) (Struct_sigma $x $u) ↪ $x;

// Grothendieck hom family (opfibration convention).                                                   // f ↦ Hom_{M(y)}(M(f)(u),v)
// For fixed (x,u) and (y,v), this is a Cat-valued functor on the hom-category Hom_B(x,y).
// Usual notation: for fixed `u ∈ M(x)` and `v ∈ M(y)`, define
//   H_{u,v} : Hom_B(x,y) ⟶ Cat
//   H_{u,v}(f) = Hom_{M(y)}(f_!(u), v).                                                               // H_{u,v}(f) = Hom_{M(y)}(M(f)(u),v)
symbol Groth_hom_fam : Π [B : Cat] (M : τ (Obj (Functor_cat B Cat_cat))),
  Π [x y : τ (Obj B)], Π (u : τ (Obj (fapp0 M x))) (v : τ (Obj (fapp0 M y))),
  τ (Obj (Functor_cat (Hom_cat x y) Cat_cat));

// β-rule: on objects f:x→y, Groth_hom_fam returns the fibre hom-category Hom_{M(y)}(M(f)(u),v).       // compute family at a base arrow
// Usual notation: `H_{u,v}(f) = Hom_{M(y)}(f_!(u), v)`.                                               // expand on objects
rule fapp0 (@Groth_hom_fam $B $M $x $y $u $v) $f
  ↪ @Hom_cat (fapp0 $M $y) (@isoFib_transport0 $B $M $x $y $f $u) $v;

// Grothendieck hom-category is itself a Grothendieck total.                                           // Hom_{∫M}((x,u),(y,v)) ≡ ∫(f ↦ Hom_{M(y)}(M(f)(u),v))
// Usual notation (opfibration Grothendieck formula):
//   Hom_{∫M}((x,u),(y,v))  ≅  ∫_{f : x→y} Hom_{M(y)}(f_!(u), v).                                       // homs in ∫M as another ∫
rule @Hom_cat (Total_cat (@IsoFibration_catd $B $M)) (Struct_sigma $x $u) (Struct_sigma $y $v)
  ↪ Total_cat (@IsoFibration_catd (Hom_cat $x $y) (@Groth_hom_fam $B $M $x $y $u $v));

// Functoriality of the base projection on hom-categories (Grothendieck).                              // π₁₁ : Hom_{∫M} → Hom_B
// Usual notation: `π₁ : ∫M → B` induces on homs a functor
//   (π₁)_{1} : Hom_{∫M}((x,u),(y,v)) ⟶ Hom_B(x,y),
//   sending `(f,α)` to `f`.                                                                           // forget the fibre component
rule @fapp1_func (Total_cat (@IsoFibration_catd $B $M)) $B (Total_proj_func (IsoFibration_catd $M))
  (Struct_sigma $x $u) (Struct_sigma $y $v)
  ↪ Total_proj_func (@IsoFibration_catd (Hom_cat $x $y) (@Groth_hom_fam $B $M $x $y $u $v));

// Sanity: objects of hom-categories in ∫M are Σ (base arrow, fibre arrow).                            // recovers the 1-cell description
assert [B : Cat] (M : τ (Obj (Functor_cat B Cat_cat)))
  [x y : τ (Obj B)] (u : τ (Obj (fapp0 M x))) (v : τ (Obj (fapp0 M y))) ⊢
  τ (Obj (@Hom_cat (Total_cat (IsoFibration_catd M)) (Struct_sigma x u) (Struct_sigma y v)))
    ≡ `τΣ_ f : τ (Obj (Hom_cat x y)),
         Obj (@Hom_cat (fapp0 M y) (@isoFib_transport0 B M x y f u) v);

// Sanity: π₁ sends a 1-cell (f,α) to its base arrow f.                                                // projection on 1-cells
assert [B : Cat] (M : τ (Obj (Functor_cat B Cat_cat)))
  [x y : τ (Obj B)] (u : τ (Obj (fapp0 M x))) (v : τ (Obj (fapp0 M y)))
  (f : τ (Obj (Hom_cat x y)))
  (α : τ (Obj (@Hom_cat (fapp0 M y) (@isoFib_transport0 B M x y f u) v))) ⊢
  fapp0
    (@fapp1_func (Total_cat (IsoFibration_catd M)) B (Total_proj_func (IsoFibration_catd M))
      (Struct_sigma x u) (Struct_sigma y v))
    (Struct_sigma f α)
    ≡ f;

// Identity in the Grothendieck total is (id_x, id_u).                                                 // id_{(x,u)} = (id_x, id_u)
rule @identity_morph (Total_cat (@IsoFibration_catd $B $M)) (Struct_sigma $x $u)
  ↪ Struct_sigma (identity_morph $B $x) (identity_morph (fapp0 $M $x) $u);

// Composition in the Grothendieck total.                                                              // (g,β) ∘ (f,α) = (g∘f, β ∘ M(g)(α))
rule @comp_fapp0 (Total_cat (@IsoFibration_catd $B $M))
  (Struct_sigma $x $u) (Struct_sigma $y $v) (Struct_sigma $z $w)
  (Struct_sigma $g $β) (Struct_sigma $f $α)
  ↪ Struct_sigma
      (@comp_fapp0 $B $x $y $z $g $f)
      (@comp_fapp0 (fapp0 $M $z)
        (@isoFib_transport0 $B $M $y $z $g (@isoFib_transport0 $B $M $x $y $f $u))
        (@isoFib_transport0 $B $M $y $z $g $v)
        $w
        $β
        (fapp0
          (@fapp1_func (fapp0 $M $y) (fapp0 $M $z)
            (fapp0 (@fapp1_func $B Cat_cat $M $y $z) $g)
            (@isoFib_transport0 $B $M $x $y $f $u) $v)
          $α));

// -------------------------------------------------------------------------------------------------
// 11. Opposite category (involution)                                                                 // A ↦ Aᵒᵖ
// -------------------------------------------------------------------------------------------------

injective symbol Op_catd : Π [X : Cat] (A : Catd X), Catd (Op_cat X);
rule Op_catd (Op_catd $A) ↪ $A;                     

// Opposite preserves terminal displayed categories.                                                  // (1_X)ᵒᵖ ≡ 1_{Xᵒᵖ}
rule @Op_catd $X (Terminal_catd $X) ↪ Terminal_catd (Op_cat $X);

// Opposite commutes with pullback (reindexing) via Op on the base functor.                            // (F^*E)ᵒᵖ ≡ (Fᵒᵖ)^*(Eᵒᵖ)
rule @Op_catd $A (@Pullback_catd $A $B $E $F)
  ↪ @Pullback_catd (Op_cat $A) (Op_cat $B) (@Op_catd $B $E) (@Op_func $A $B $F);

// Opposite of a total category is the total of the opposite displayed category.                      // (∫E)ᵒᵖ ≡ ∫(Eᵒᵖ)
rule Op_cat (Total_cat $E) ↪ Total_cat (Op_catd $E);

// The projection of the opposite total is the opposite of the projection.                            // (π₁)ᵒᵖ ≡ π₁
rule @Op_func (Total_cat $E) $B (@Total_proj_func $B $E)
  ↪ @Total_proj_func (Op_cat $B) (@Op_catd $B $E);

// Sanity: opposites interact with core constructions by definitional rewriting.                      // exercise Op rules
assert [A B : Cat] (E : Catd B) (F : τ (Obj (Functor_cat A B))) ⊢
  @Op_catd A (@Pullback_catd A B E F)
    ≡ @Pullback_catd (Op_cat A) (Op_cat B) (@Op_catd B E) (@Op_func A B F);

assert [B : Cat] (E : Catd B) ⊢ Op_cat (Total_cat E) ≡ Total_cat (Op_catd E);

assert [B : Cat] (E : Catd B) ⊢
  @Op_func (Total_cat E) B (@Total_proj_func B E)
    ≡ @Total_proj_func (Op_cat B) (@Op_catd B E);

// -------------------------------------------------------------------------------------------------
// 12. Terminal category and “constant functors from the terminal”                                   // 1 and points as functors
// -------------------------------------------------------------------------------------------------

// The terminal category 1 (one object, one morphism).                                                // categorical unit
constant symbol Terminal_cat : Cat;                                                                  // 1 : Cat

// Terminal category is self-dual.                                                                    // 1ᵒᵖ ≡ 1
rule Op_cat Terminal_cat ↪ Terminal_cat;

// The unique functor A → 1 (terminal functor).                                                       // ! : A → 1
injective symbol Terminal_func : Π (A : Cat), τ (Obj (Functor_cat A Terminal_cat));                      // object of Functor_cat(A,1)

// Opposite of the terminal functor is the terminal functor out of Aᵒᵖ.                                // (!:A→1)ᵒᵖ ≡ !:Aᵒᵖ→1
rule @Op_func $A Terminal_cat (@Terminal_func $A) ↪ @Terminal_func (Op_cat $A);

// Distinguished object * : Obj(1) (everything is definitionally equal to it via rules if desired).  // point of the terminal category
constant symbol Terminal_obj : τ (Obj Terminal_cat);                                                 // * : Obj(1)

// “Object as functor”: an object y:Obj(Y) induces a functor 1 → Y selecting y.                       // points as functors
injective symbol Obj_func : Π [Y : Cat], τ (Obj Y) → τ (Obj (Functor_cat Terminal_cat Y));               // y ↦ (1→Y) picking y

// Opposite of a point-functor is the point-functor into the opposite category.                       // (y:1→Y)ᵒᵖ : 1→Yᵒᵖ
rule @Op_func Terminal_cat $Y (@Obj_func $Y $y) ↪ @Obj_func (Op_cat $Y) $y;

// Computation: applying the point-functor to the unique object of 1 yields the point.                // evaluation at *
rule fapp0 (Obj_func $F) $M ↪ $F;                                                                    // (const F)(*) ↪ F (for any * in 1)

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
    A : Cat    ↦    Lift_catd1(A) : Catd(1)
  i.e. the constant fibration over the terminal category.
*/

// View an ordinary category as a displayed category over the terminal base.                          // constant family over 1
injective symbol Lift_catd1 : Cat → Catd Terminal_cat;                                                // A ↦ const_1(A)

// Opposite of a constant family is constant on the opposite category.                                // const(A)ᵒᵖ ≡ const(Aᵒᵖ)
rule @Op_catd Terminal_cat (Lift_catd1 $A) ↪ Lift_catd1 (Op_cat $A);

// The Grothendieck construction of a constant family over 1 is definitionally the original category. // ∫(const_1(A)) ≡ A
rule Total_cat (Lift_catd1 $A) ↪ $A;

// The base projection of ∫(const_1(A)) → 1 is the terminal functor A → 1.                            // π₁ ↪ !
rule Total_proj_func (Lift_catd1 $A) ↪ Terminal_func $A;

// Fibres of a constant family are constant (independent of the base point in 1).                    // fibre(const_1(A),*) ≡ A
rule Fibre_cat (Lift_catd1 $A) _ ↪ $A;

// Lift an ordinary functor to a displayed functor between constant families over 1.                 // Functor ↦ displayed Functor over 1
injective symbol Lift_funcd1 : Π [A B : Cat],
  τ (Obj (Functor_cat A B)) → τ (Obj (Functord_cat (Lift_catd1 A) (Lift_catd1 B)));

// Forget a displayed functor between constant families by taking its induced functor on totals.     // displayed-over-1 ↦ ordinary
symbol Unlift_func1 [A B : Cat]
  (FF : τ (Obj (Functord_cat (Lift_catd1 A) (Lift_catd1 B)))) : τ (Obj (Functor_cat A B))
≔ @Total_intro_func Terminal_cat (Lift_catd1 A) (Lift_catd1 B) FF;
// NOTE: definitional abbreviation; keep in mind the same “rewrite head” principle as for `tapp0_fapp0` if we later want to normalize by rewriting at `Unlift_func1 ...`.

// // β-law: unlift∘lift is definitional (on functors).                                                  // ∫(lift(F)) ↪ F
rule @Total_intro_func Terminal_cat (Lift_catd1 $A) (Lift_catd1 $B) (Lift_funcd1 $F) ↪ $F;


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
constant symbol prod_cat : τ (Obj (Functor_cat (Product_cat Cat_cat Cat_cat) Cat_cat));

// Object-action: prod_cat₀(A,B) ≡ A×B.                                                                // fapp0(prod_cat,(A,B)) ↪ Product_cat(A,B)
rule @fapp0 (Product_cat Cat_cat Cat_cat) Cat_cat prod_cat (Struct_sigma $A $B)
  ↪ Product_cat $A $B;

// Sanity: prod_cat acts pointwise as categorical product.                                             // prod_cat(A,B) = A×B
assert (A B : Cat) ⊢ fapp0 prod_cat (Product_pair A B) ≡ Product_cat A B;

// Hom-categories of the product compute pointwise on projections.                                   // Hom_{A×B}(P,Q) ≡ Hom_A(π₁P,π₁Q) × Hom_B(π₂P,π₂Q)
rule @Hom_cat (Product_cat $A1 $A2) $P $Q
  ↪ Product_cat (@Hom_cat $A1 (sigma_Fst $P) (sigma_Fst $Q))
                (@Hom_cat $A2 (sigma_Snd $P) (sigma_Snd $Q));

// Identity and composition in a product category are computed componentwise (on paired endpoints).   // id and ∘ in A×B
rule @identity_morph (Product_cat $A1 $A2) (Struct_sigma $X1 $X2)
  ↪ Struct_sigma (@identity_morph $A1 $X1) (@identity_morph $A2 $X2);

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

    - For Grothendieck displayed categories `IsoFibration_catd E` coming from `E : Z ⟶ Cat`, we do
      have canonical Σ-descriptions of objects and morphisms in their total categories ∫E.

  Implementation:
    - We internalize categorical product as `prod_cat : Cat×Cat ⟶ Cat` and introduce a primitive
      head `prod_func` for pointwise product of Cat-valued functors.
    - Then we add the key computation rule:
        Product_catd( IsoFibration_catd E, IsoFibration_catd D )  ↪  IsoFibration_catd (prod_func E D)
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
// Design note: `prod_func` is a primitive *rewrite head* (not a definitional abbreviation).           // keep a stable head for rewriting
// Motivation (same pattern as `tapp0_fapp0` and `isoFib_transport0`):
//   - A definition `prod_func E D ≔ (prod_cat) ∘ ⟨E,D⟩` would expand to a large `comp_fapp0`
//     term in `Cat_cat`, which is expensive/fragile to unfold inside other rewrite rules.
//   - Making `prod_func` primitive gives a small, stable head so rules like
//       Product_catd(∫E,∫D) ↪ ∫(E×D)
//     can fire without forcing Lambdapi to normalize a big functor-composition expression.
symbol prod_func [Z : Cat]
  (E D : τ (Obj (Functor_cat Z Cat_cat))) : τ (Obj (Functor_cat Z Cat_cat));

// Pointwise computation on objects: (E×D)(z) ↦ E(z)×D(z).                                             // fapp0(prod_func(E,D),z) ↪ Product_cat(E(z),D(z))
rule fapp0 (prod_func $E $D) $z ↪ Product_cat (fapp0 $E $z) (fapp0 $D $z);

// Sanity: prod_func agrees pointwise with postcomposition by prod_cat.                                // (E×D)(z) = prod_cat(E(z),D(z))
assert [Z : Cat] (E D : τ (Obj (Functor_cat Z Cat_cat))) (z : τ (Obj Z)) ⊢
  fapp0 (prod_func E D) z ≡ fapp0 prod_cat (Struct_sigma (fapp0 E z) (fapp0 D z));

// Fibrewise product of Grothendieck displayed categories is Grothendieck of pointwise product.        // ∫E ×_Z ∫D  ≅  ∫(E×D)
// If `E,D : Z ⟶ Cat` are Cat-valued functors, then their Grothendieck constructions are displayed
// categories `IsoFibration_catd E, IsoFibration_catd D : Catd Z`. Their fibrewise product over `Z`
// is again a Grothendieck displayed category, classified by the pointwise product functor:
//   (E ⊗ D)(z) = E(z) × D(z).
rule @Product_catd $Z (@IsoFibration_catd $Z $E) (@IsoFibration_catd $Z $D)
  ↪ @IsoFibration_catd $Z (prod_func $E $D);

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
  τ (Obj (Functor_cat (Product_cat (Hom_cat Y_A Z_A) (Hom_cat X_A Y_A)) (Hom_cat X_A Z_A)));                           // an object in the functor-category

// Computation: applying the composition functor to a pair (g,f) returns the composite g∘f.           // β-rule for composition functor
rule (fapp0 (@comp_func $A $X $Y $Z)) (Struct_sigma $g $f) ↪ @comp_fapp0 $A $X $Y $Z $g $f; // compose(g,f) ↪ g∘f

// Sanity check: the β-rule is visible at the level of definitional equality / conversion.            // exercise the rule
assert [A : Cat] [X Y : τ (Obj A)] [Z : τ (Obj A)]
  (g : τ (Obj (Hom_cat Y Z))) (f : τ (Obj (Hom_cat X Y))) ⊢
  fapp0 (@comp_func A X Y Z) (Struct_sigma g f) ≡ @comp_fapp0 A X Y Z g f;

// Composition of functors is composition in Cat_cat (a special case of comp_fapp0).         // categorical composition in Cat
symbol compFunc [A B : Cat] [C:Cat]                                                       // A,B,C : Cat
  (F: τ (Obj (Functor_cat B C))) (G: τ (Obj (Functor_cat A B))) : τ (Obj (Functor_cat A C))                      // F∘G : Functor_cat(A,C)
≔ @comp_fapp0 Cat_cat _ _ _ F G;                                                             // compose in Cat_cat
// NOTE: definitional abbreviation; if we later want pointwise computation rules with head `compFunc`, refactor to an uninterpreted symbol + rewrite rules (cf. tapp0_fapp0).

// -------------------------------------------------------------------------------------------------
// 16. Draft: “simplicial” view on higher morphisms via slice-like dependent functors                // experiments / TODO zone
// -------------------------------------------------------------------------------------------------

// TODO: implement contravariant hom (`hom_con`) and opposites coherently (requires Op_cat functoriality). // dual Yoneda
// TODO: add explicit “globular” source/target operations and interchange/composition laws.          // ω-category axioms
// TODO: connect with Kosta Došen's “stacking” (horizontal composition of 2-cells along a 1-cell).   // 2-simplex / 3-simplex diagrams

// Dependent Yoneda/hom for a dependent category: “Hom_cat in the fibre / in a slice”.                   // dependent hom (2-simplex / triangle classifier)
constant symbol homd_cov : Π [Z : Cat], Π [E : Catd Z], Π [W_Z: τ (Obj Z)]                             // base Z, displayed E, base object W_Z
  (W_EW : τ (Obj (Fibre_cat E W_Z))), Π [D : Catd Z], Π (FF : τ (Obj (Functord_cat D E))),               // W in fibre, D another displayed cat, FF : D→E
  τ (Obj (Functor_cat (Total_cat (Product_catd D (IsoFibration_catd ( compFunc op (hom_cov W_Z (@Id_func Z)) )))) // source category (a total category)
                Cat_cat));                                                                            // target category Cat_cat (Cat-valued functors)

// Application of a dependent functor on objects, fibrewise.                                         // fibred fapp0
symbol fdapp0 : Π [Z : Cat], Π [E D : Catd Z], Π (FF : τ (Obj (Functord_cat E D))),          // dependent functor FF : E→D
  Π [X_Z : τ (Obj Z)], τ (Obj (Fibre_cat E X_Z)) → τ (Obj (Fibre_cat D X_Z));                         // map objects in each fibre

// Special case: fdapp0 of a lifted ordinary functor is ordinary object-application (fibrewise).      // fdapp0(lift(F)) ↪ fapp0(F)
// NOTE: the base point in Z is an *implicit* argument of `fdapp0`, hence the `[ _ ]`.
rule fdapp0 (Lift_funcd1 $F) [_] $x ↪ fapp0 $F $x;

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
//   (`IsoFibration_catd E0`, `IsoFibration_catd D0`), because the transport `f_!(W)` uses the strict
//   opfibration-style object transport `isoFib_transport0` induced by a Cat-valued functor.           // keep Catd semantic, compute only for ∫(−)
//
// Here the input object is written in the normal form produced by the Grothendieck/product rules:
//   (z,(d,f)) is encoded as `Struct_sigma z (Struct_sigma d f)`, where
//     • `z : Ob(Z)`,
//     • `d : Ob(D(z))`,
//     • `f : Ob(Hom_Z(W_Z, z))` (the base edge along which we transport W).
rule fapp0 (@homd_cov $Z (@IsoFibration_catd $Z $E0) $W_Z $W
              (@IsoFibration_catd $Z $D0) $FF)
            (Struct_sigma $z (Struct_sigma $d $f))
  ↪ Hom_cat
      (@isoFib_transport0 $Z $E0 $W_Z $z $f $W)
      (fdapp0 $FF [$z] $d);

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
         (Hom_cat (fapp0 F_AB Y_A) (fapp0 G_AB Y_A))));

// Object-action of `tapp0_func`: compute the 1-cell component ϵ_Y by evaluating ϵ^Y at id_Y.         // component extraction
symbol tapp0_fapp0 : Π [A B : Cat], Π [F_AB G_AB : τ (Obj (Functor_cat A B))],
  Π (Y_A : τ (Obj A)), Π (ϵ : τ (Obj (Transf_cat F_AB G_AB))),
  τ (Obj (Hom_cat (fapp0 F_AB Y_A) (fapp0 G_AB Y_A)));

/*
  Design note: `tapp0_fapp0` is intentionally *not* defined by `≔ ...`.

  Motivation:
  - In the 1-category development (emdash.lp), the “pointwise” operations (like component extraction)
    are *rewrite heads*, so we can later add computation rules directly on them (and keep proof scripts small).
  - If we made `tapp0_fapp0` a definitional abbreviation (`≔ fdapp0 ...`), then rewriting would first unfold it,
    and we would lose the ability to conveniently attach further rewrite rules to the head symbol `tapp0_fapp0`.

  Hence, we declare `tapp0_fapp0` as a primitive operation and give its current computation as a rewrite rule.
*/

// Computation: ϵ_Y is obtained by evaluating ϵ^Y at id_Y.                                             // tapp0_fapp0 ↪ eval(tapp1_fapp0_funcd, id_Y)
rule @tapp0_fapp0 $A $B $F_AB $G_AB $Y_A $ϵ
  ↪ fdapp0 (@tapp1_fapp0_funcd $A $B $F_AB $G_AB $Y_A $ϵ) [$Y_A] (identity_morph $A $Y_A);

// β-rule: `tapp0_fapp0` is definitionally the object-action of the functor `tapp0_func`.            // unpack tapp0_func at objects
rule fapp0 (@tapp0_func $A $B $F_AB $G_AB $Y_A) $ϵ ↪ @tapp0_fapp0 $A $B $F_AB $G_AB $Y_A $ϵ;

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
  ↪ @tapp0_fapp0 $I $A1 (Product_projL_func $F) (Product_projL_func $G) $X (Product_projL_transf $ϵ);

rule sigma_Snd (@tapp0_fapp0 $I (Product_cat $A1 $A2) $F $G $X $ϵ)
  ↪ @tapp0_fapp0 $I $A2 (Product_projR_func $F) (Product_projR_func $G) $X (Product_projR_transf $ϵ);

rule @tapp0_fapp0 $I (Product_cat $A1 $A2)
  (Product_pair_func $F1 $F2) (Product_pair_func $G1 $G2) $X (Product_pair_transf $ϵ1 $ϵ2)
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
  Π (f : τ (Obj (Hom_cat X Y1))), Π (g : τ (Obj (Hom_cat Y1 Y2))), Π (ϵ : τ (Obj (Transf_cat F_AB G_AB))),
  τ (Obj
      (@Hom_cat (Hom_cat (fapp0 F_AB X) (fapp0 G_AB Y2))
        // source 1-cell: G(g) ∘ ηᵋ_f  (transport ηᵋ_f along g so it lands in Hom_B(FX, GY₂))
        (@comp_fapp0 B (fapp0 F_AB X) (fapp0 G_AB Y1) (fapp0 G_AB Y2)
          (fapp0 (@fapp1_func A B G_AB Y1 Y2) g)
          (@fdapp0 A
            (IsoFibration_catd (hom_cov X (@Id_func A)))
            (IsoFibration_catd (hom_cov (fapp0 F_AB X) G_AB))
            (@tapp1_fapp0_funcd A B F_AB G_AB X ϵ)
            Y1
            f))
        // target 1-cell: ηᵋ_{g∘f}
        (@fdapp0 A
          (IsoFibration_catd (hom_cov X (@Id_func A)))
          (IsoFibration_catd (hom_cov (fapp0 F_AB X) G_AB))
          (@tapp1_fapp0_funcd A B F_AB G_AB X ϵ)
          Y2
          (@comp_fapp0 A X Y1 Y2 g f))));

// “Slice-category” / simplicial action: fapp1_funcd packages fapp1_func as a dependent functor over representables. // 2-simplex intuition
// Motivation: complements the globular iteration (Hom_cat(X,Y) : Cat) with a simplicial iteration (fibrewise). // 2- and 3-simplex pictures
symbol fapp1_funcd : Π [A B : Cat], Π (F_AB : τ (Obj (Functor_cat A B))), Π [X_A: τ (Obj A)],         // functor and outer index
  τ (Obj (Functord_cat (IsoFibration_catd (hom_cov X_A (@Id_func A)))                              // source displayed: Hom_A(X_A,-)
                  (IsoFibration_catd (hom_cov (fapp0 F_AB X_A) F_AB))));                                // target displayed: Hom_B(FX_A, F_AB(-))

// Link: the object-action fdapp0 of fapp1_funcd reduces to applying fapp1_func on a morphism-object.           // coherence rule between globular & simplicial views
rule fdapp0 (@fapp1_funcd $A $B $F $X) $f
  ↪ fapp0 (fapp1_func [$A] [$B] $F [$X] [_]) $f;                                                        // fdapp0(fapp1_funcd(F,X),f) ↪ fapp0(fapp1_func(F,X,Y),f)

// Sanity: the link rule fires at the level of definitional equality.                                            // exercise the rule
assert [A B : Cat] (F : τ (Obj (Functor_cat A B))) (X Y : τ (Obj A)) (f : τ (Obj (Hom_cat X Y))) ⊢
  fdapp0 (fapp1_funcd F [X]) [Y] f ≡ fapp0 (fapp1_func F [X] [Y]) f;

// Application of a dependent functor on morphisms (still draft: depends on `homd_cov`).              // fibred fapp1_func
symbol fdapp1_funcd : Π [Z : Cat], Π [A B : Catd Z], Π (F : τ (Obj (Functord_cat A B))),          // dependent functor F : A→B
  Π [X_: τ (Obj Z)] (X: τ (Obj (Fibre_cat A X_))),                                                    // base object X_ and fibre object X
  τ (Obj (Functord_cat (IsoFibration_catd (homd_cov X (@Id_funcd _ A)))                            // source hom in fibre (placeholder)
                  (IsoFibration_catd (homd_cov (fdapp0 F X) F))));                                     // target hom in fibre (placeholder)

// Dependent transformations between dependent functors (displayed natural transformations).          // displayed transfors
constant symbol Transfd_cat : Π [Z : Cat], Π [E D : Catd Z],                                 // base and displayed categories
  Π (FF GG : τ (Obj (Functord_cat E D))), Cat;                               // Transfd_cat(FF,GG) : Cat

/*
  tdapp1_func_funcd is the displayed analogue of tapp1_func_funcd.

  Again, the binders (X_Z, U_EX) are *external* projection indices:
  - X_Z : Obj(Z) picks a fibre of the displayed category E : Catd(Z),
  - U_EX : Obj(Fibre_cat E X_Z) is the point *inside that fibre* at which we project components.

  Think “superscripted component”: for ϵ : Transfd_cat(F,G), we get ϵ^(X_,X) as a dependent functor between
  displayed representables. This is the step that makes iteration possible:
  modifications between displayed transfors project to transfors between these component-functors, etc.
*/
symbol tdapp1_func_funcd : Π [Z : Cat], Π [E D : Catd Z], Π [FF GG : τ (Obj (Functord_cat E D))],        // dependent functors FF,GG
Π (X_Z: τ (Obj Z)) (U_EX: τ (Obj (Fibre_cat E X_Z))),                                                  // component at fibre object U_EX
   τ (Obj (Functor_cat (Transfd_cat FF GG)
          (Functord_cat (IsoFibration_catd (homd_cov U_EX (@Id_funcd _ E)))                         // source hom (placeholder)
                    (IsoFibration_catd (homd_cov (fdapp0 FF U_EX) GG)))));                               // target hom (placeholder)

// `tdapp1_fapp0_funcd` is the fapp0 part of `tdapp1_func_funcd`
symbol tdapp1_fapp0_funcd : Π [Z : Cat], Π [E D : Catd Z], Π [FF GG : τ (Obj (Functord_cat E D))],        // dependent functors FF,GG
Π (X_Z: τ (Obj Z)) (U_EX: τ (Obj (Fibre_cat E X_Z))),                                                  // component at fibre object U_EX
  Π (ϵ : τ (Obj (Transfd_cat FF GG))),
  τ (Obj (Functord_cat (IsoFibration_catd (homd_cov U_EX (@Id_funcd _ E)))                         // source hom (placeholder)
                  (IsoFibration_catd (homd_cov (fdapp0 FF U_EX) GG))));                                 // target hom (placeholder)

// β-rule: `tdapp1_fapp0_funcd` is definitionally the object-action of the functor `tdapp1_func_funcd`.             // unpack tdapp1_func_funcd at objects
rule fapp0 (@tdapp1_func_funcd $Z $E $D $FF $GG $X_Z $U_EX) $ϵ ↪ @tdapp1_fapp0_funcd $Z $E $D $FF $GG $X_Z $U_EX $ϵ;

// Key identification: the hom-category of the functor-category is the transformation-category.      // Hom_{Functor_cat(A,B)}(F,G) ≅ Transf_cat(F,G)
rule @Hom_cat (Functord_cat _ _) $F $G ↪ Transfd_cat $F $G;                                                        // definitional equality of homs

// The action of a displayed (2-)transformation on a displayed (3-)modification: fapp1_func-part of `tdapp1_func_funcd`. // displayed “components of components”
symbol tdapp1_fapp1_func : Π [Z : Cat], Π [E D : Catd Z], Π [FF GG : τ (Obj (Functord_cat E D))],       // base+displayed cats and functors
  Π (X_Z : τ (Obj Z)) (U_EX : τ (Obj (Fibre_cat E X_Z))),                                                  // external projection index (in a fibre)
  Π [ϵ : τ (Obj (Transfd_cat FF GG))], Π [ϵ' : τ (Obj (Transfd_cat FF GG))],                                        // displayed transfors ϵ ⇒ ϵ'
  τ (Obj (Functor_cat (@Hom_cat (Transfd_cat FF GG) ϵ ϵ')                                                               // displayed modifications between ϵ and ϵ'
                 (Transfd_cat (tdapp1_fapp0_funcd X_Z U_EX ϵ) (tdapp1_fapp0_funcd X_Z U_EX ϵ'))));                             // displayed transfors between components

// β-rule: `tdapp1_fapp1_func` is definitionally the hom-action of the functor `tdapp1_func_funcd`.                // unpack tdapp1_func_funcd at homs
rule @fapp1_func _ _ (@tdapp1_func_funcd $Z $E $D $FF $GG $X_Z $U_EX) $ϵ $ϵ'
  ↪ @tdapp1_fapp1_func $Z $E $D $FF $GG $X_Z $U_EX $ϵ $ϵ';

// The action of a (2-)transformation on a (3-)modification: fapp1_func-part of `tapp1_func_funcd`.               // “components of components”
// If α : Hom_{Transf_cat(F,G)}(ϵ,ϵ') is a modification, then `tapp1_fapp1_func X ϵ ϵ'` transports α to a        // functoriality of component-evaluation
// dependent transformation between the dependent functors `tapp1_fapp0_funcd X ϵ` and `tapp1_fapp0_funcd X ϵ'`.     // (codomain hom is Transfd_cat by the rule above)
symbol tapp1_fapp1_func : Π [A B : Cat], Π [F_AB G_AB : τ (Obj (Functor_cat A B))],                     // base categories and functors
  Π (X_A : τ (Obj A)),                                                                                   // external projection index
  Π [ϵ : τ (Obj (Transf_cat F_AB G_AB))], Π [ϵ' : τ (Obj (Transf_cat F_AB G_AB))],                               // transformations ϵ ⇒ ϵ'
  τ (Obj (Functor_cat (@Hom_cat (Transf_cat F_AB G_AB) ϵ ϵ')                                                          // modifications between ϵ and ϵ'
                 (Transfd_cat (tapp1_fapp0_funcd X_A ϵ) (tapp1_fapp0_funcd X_A ϵ'))));                                      // dependent transf between components

// β-rule: `tapp1_fapp1_func` is definitionally the hom-action of the functor `tapp1_func_funcd`.                  // unpack tapp1_func_funcd at homs
rule @fapp1_func _ _ (@tapp1_func_funcd $A $B $F_AB $G_AB $X_A) $ϵ $ϵ'
  ↪ @tapp1_fapp1_func $A $B $F_AB $G_AB $X_A $ϵ $ϵ';


// -------------------------------------------------------------------------------------------------
// 17. Sanity checks (lightweight “unit tests” for rewrite normalization)                             // keep small, avoids proof noise
// -------------------------------------------------------------------------------------------------

// Op_cat involution reduces by rewriting.                                                            // checks Op_cat rule fires
assert ⊢ Op_cat (Op_cat Cat_cat) ≡ Cat_cat;                                                          // (Cat_catᵒᵖ)ᵒᵖ ≡ Cat_cat

// Identity functor on objects reduces by rewriting.                                                  // checks fapp0(Id_func) β-rule
compute fapp0 (@identity_morph Cat_cat Terminal_cat) Terminal_obj;                                    // normal form should be `Terminal_obj`

// tapp1_func_funcd object-action reduces to tapp1_fapp0_funcd by rewriting.                                         // checks tapp β-rule fires
assert [A B : Cat] [F_AB G_AB : τ (Obj (Functor_cat A B))] (X_A : τ (Obj A)) (ϵ : τ (Obj (Transf_cat F_AB G_AB))) ⊢
  fapp0 (tapp1_func_funcd X_A) ϵ ≡ tapp1_fapp0_funcd X_A ϵ;

// tapp0_fapp0 is the derived “component at Y” (evaluation at id_Y) and reduces by rewriting.          // checks tapp0 β-rule fires
assert [A B : Cat] [F_AB G_AB : τ (Obj (Functor_cat A B))] (Y_A : τ (Obj A)) (ϵ : τ (Obj (Transf_cat F_AB G_AB))) ⊢
  fapp0 (tapp0_func Y_A) ϵ ≡ tapp0_fapp0 Y_A ϵ;

// tdapp1_func_funcd object-action reduces to tdapp1_fapp0_funcd by rewriting.                                       // checks tdapp β-rule fires
assert [Z : Cat] [E D : Catd Z] [FF GG : τ (Obj (Functord_cat E D))]
  (X_Z : τ (Obj Z)) (U_EX : τ (Obj (Fibre_cat E X_Z))) (ϵ : τ (Obj (Transfd_cat FF GG))) ⊢
  fapp0 (tdapp1_func_funcd X_Z U_EX) ϵ ≡ tdapp1_fapp0_funcd X_Z U_EX ϵ;

// tapp1_func_funcd hom-action reduces to tapp1_fapp1_func by rewriting (uses @Hom_cat(Functord_cat..) ≡ Transfd_cat).        // checks tapp fapp1_func β-rule fires
assert [A B : Cat] [F_AB G_AB : τ (Obj (Functor_cat A B))] (X_A : τ (Obj A))
  (ϵ : τ (Obj (Transf_cat F_AB G_AB))) (ϵ' : τ (Obj (Transf_cat F_AB G_AB))) ⊢
  @fapp1_func _ _ (tapp1_func_funcd X_A) ϵ ϵ' ≡ @tapp1_fapp1_func A B F_AB G_AB X_A ϵ ϵ';

// tdapp1_func_funcd hom-action reduces to tdapp1_fapp1_func by rewriting.                                         // checks tdapp fapp1_func β-rule fires
assert [Z : Cat] [E D : Catd Z] [FF GG : τ (Obj (Functord_cat E D))]
  (X_Z : τ (Obj Z)) (U_EX : τ (Obj (Fibre_cat E X_Z)))
  (ϵ : τ (Obj (Transfd_cat FF GG))) (ϵ' : τ (Obj (Transfd_cat FF GG))) ⊢
  @fapp1_func _ _ (tdapp1_func_funcd X_Z U_EX) ϵ ϵ' ≡ @tdapp1_fapp1_func Z E D FF GG X_Z U_EX ϵ ϵ';

// Pullback of a Grothendieck isofibration reduces to Grothendieck of precomposition.                 // checks Pullback_catd/∫ rewrite fires
assert [A B : Cat] (E : τ (Obj (Functor_cat B Cat_cat))) (F : τ (Obj (Functor_cat A B))) ⊢
  @Pullback_catd A B (@IsoFibration_catd B E) F
    ≡ @IsoFibration_catd A (@comp_fapp0 Cat_cat A B Cat_cat E F);

// Casting Cat to Catd(1) behaves as expected.                                                        // checks Lift_catd1/Lift_funcd1 rules fire
assert [A : Cat] ⊢ Total_cat (Lift_catd1 A) ≡ A;
assert [A : Cat] (x1 : τ (Obj Terminal_cat)) ⊢ Fibre_cat (Lift_catd1 A) x1 ≡ A;
assert [A B : Cat] (F : τ (Obj (Functor_cat A B))) ⊢ Unlift_func1 (Lift_funcd1 F) ≡ F;
assert [A B : Cat] (F : τ (Obj (Functor_cat A B))) (x1 : τ (Obj Terminal_cat)) (x : τ (Obj A)) ⊢
  fdapp0 (Lift_funcd1 F) [x1] x ≡ fapp0 F x;
