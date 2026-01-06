/*
  m— / emdash2                                                                 // project name (“m—” / “emdash”), version 2
  Functorial programming for (strict/lax) ω-categories in Lambdapi.             // overall intent: ω-categories, ω-functors, ω-transformations

  Design note: this file is intentionally “kernel-like”.                        // we keep primitives small and rewrite/unif rules explicit
  Comments aim to align names with standard category-theory terms.              // helps IDE autocompletion and cross-referencing textbooks/wikis
*/                                                                              // end header

flag "eta_equality" on;                                                         // enable η-reduction in definitional equality (normalization)

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
// 4. Categories as a classifier `Cat : TYPE` with `Obj : Cat → Grpd` and `Hom : ... → Cat`          // strict ω-category skeleton
// -------------------------------------------------------------------------------------------------

constant symbol Cat : TYPE;                                                                         // classifier of (strict/lax) ω-categories

// Objects of a category form a groupoid (`Grpd`), not just a set.                                   // higher-categorical “objects up to paths”
injective symbol Obj : Cat → Grpd;                                                                  // object classifier of a category

// Hom is itself a category: for X,Y : Obj(A), Hom_A(X,Y) : Cat.                                     // hom-categories (enriched/globular view)
injective symbol Hom : Π [A : Cat] (X: τ (Obj A)) (Y: τ (Obj A)), Cat;                              // hom-category as a Cat

// Identity morphism: an object in the hom-category Hom_A(X,X).                                      // identity 1-cell (and higher units implicitly)
injective symbol identity_morph : Π (A : Cat), Π (X: τ (Obj A)), τ (Obj (Hom X X));                 // id_X : Obj(Hom(X,X))

/*
  OBSERVATION (cartierSolution13.lp vs emdash.lp, and why emdash2/emdash3 keep *both* forms):

  - In cartierSolution13.lp, many core constructions are "objects in functor categories", i.e. functors
    `A → B` (and then transformations between them). This is the "parametric/object-in-context" view:
      F : Obj(Functor(A,B))  behaves like "an object of B in the context A".

  - In emdash.lp (1-category draft), one often works directly with "pointwise" data:
      a : Hom(X,Y)   (a single 1-cell, 0-dimensional as data),
    and then adds rewrite/unification rules so computation is easy.

  - In emdash2/emdash3 (ω-categories), `Hom_A(X,Y)` is itself a category, so a "morphism" X→Y is
    an *object* of that hom-category: `Obj(Hom_A(X,Y))`. Higher morphisms live in the hom-category too.

  This creates a useful tension:
  (1) the *internal/semantic* composition is best packaged as a *functor*
        ∘ : Hom(Y,Z) × Hom(X,Y) → Hom(X,Z)
      i.e. an object of `Functor(Product_cat(Hom Y Z)(Hom X Y)) (Hom X Z)`.
      This is faithful to the ω-story: functoriality (and hence higher coherence) is "baked in" by typing.

  (2) the *computational/pointwise* composition is the "application at objects" of that functor:
        compose_morph_fapp0 g f : Obj(Hom(X,Z)).
      This is the handle on which we can hang rewrite/unification rules (as we did in emdash.lp).

  Below, `compose_morph_fapp0` is the pointwise operation, and `compose_morph` is the functorial packaging.
  The rewrite rule later ("β-rule for composition functor") connects them.
*/

// Composition at object-level in a hom-category: (g : Hom(Y,Z)) and (f : Hom(X,Y)) compose to Hom(X,Z). // pointwise / computational
symbol compose_morph_fapp0 : Π [A : Cat], Π [X: τ (Obj A)], Π [Y: τ (Obj A)], Π [Z: τ (Obj A)],     // ambient A and objects X,Y,Z
  Π (g: τ (Obj (Hom Y Z))), Π (f: τ (Obj (Hom X Y))),                                                // composable morphisms g ∘ f
  τ (Obj (Hom X Z));                                                                                // composite morphism in Hom(X,Z)

// -------------------------------------------------------------------------------------------------
// 5. Functors (as objects of a functor-category `Functor A B : Cat`)                                // ω-functors
// -------------------------------------------------------------------------------------------------

// The “functor category” between A and B (objects are functors, morphisms are transformations).     // internal functor category
constant symbol Functor : Π (A : Cat), Π (B : Cat), Cat;                                            // Functor(A,B) : Cat

// Action of a functor on objects.                                                                   // F₀ : Obj(A) → Obj(B)
symbol fapp0 : Π [A : Cat], Π [B : Cat], Π (F : τ (Obj (Functor A B))),                              // functor object F ∈ Obj(Functor(A,B))
  τ (Obj A) → τ (Obj B);                                                                            // send X ↦ F(X)

// Action of a functor on hom-categories: gives a functor Hom_A(X,Y) → Hom_B(FX,FY).                 // F₁ as a functor (ω-level)
symbol fapp1 : Π [A : Cat], Π [B : Cat], Π (F : τ (Obj (Functor A B))),                              // functor object F
  Π [X: τ (Obj A)], Π [Y: τ (Obj A)],                                                               // endpoints X,Y
  τ (Obj (Functor (Hom X Y) (Hom (fapp0 F X) (fapp0 F Y))));                                         // functor on the hom-category

// -------------------------------------------------------------------------------------------------
// 6. Classifier categories: `Grpd_cat` and `Cat_cat` (categories of groupoids and categories)       // “universes as categories”
// -------------------------------------------------------------------------------------------------

// `Grpd_cat` plays the role of the category of groupoids/sets (discrete fibrations classifier).     // analogue of Set/Type-as-a-category
constant symbol Grpd_cat : Cat;                                                                     // category of ∞-groupoids
unif_rule τ (Obj $A) ≡ Grpd ↪ [ $A ≡ Grpd_cat ];                                                     // infer A ≡ Grpd_cat when Obj(A) decodes to Grpd
rule τ (Obj (@Hom Grpd_cat $X $Y)) ↪ (τ $X → τ $Y);                                                  // morphisms in Grpd_cat are functions

// `Cat_cat` is the category of categories (fibrations classifier).                                  // Cat of categories
constant symbol Cat_cat : Cat;                                                                      // category of categories
unif_rule τ (Obj $A) ≡ Cat ↪ [ $A ≡ Cat_cat ];                                                       // infer A ≡ Cat_cat when Obj(A) decodes to Cat
rule @Hom Cat_cat $X $Y ↪ Functor $X $Y;                                                            // morphisms in Cat_cat are functors

// Identity functor on a category A (as an object in Functor(A,A)).                                  // 1-category identity, lifted to ω setting
symbol identity_functor [A: Cat] : τ (Obj (Functor A A))                                             // identity functor id_A : Obj(Functor(A,A))
≔ @identity_morph Cat_cat A;                                                                        // defined as identity morphism in Cat_cat
rule fapp0 (@identity_morph Cat_cat $A) $xA ↪ $xA;                                                   // computation: (id_A)(x) ↪ x

// Covariant “hom functor” / Yoneda-style precomposition: Hom_A(W, F(-)).                             // hom-covariant / representable functor core
constant symbol hom_cov : Π [A : Cat], Π (W: τ (Obj A)), Π [B : Cat],                                // W ∈ Obj(A), F : Functor(B,A)
  Π (F : τ (Obj (Functor B A))), τ (Obj (Functor B Cat_cat));                                       // result: B → Cat_cat (a Cat-valued functor)
rule fapp0 (hom_cov $X $F) $Y ↪ Hom $X (fapp0 $F $Y);                                                // object action: Y ↦ Hom_A(X, F(Y))

// Naturality w.r.t. precomposition in the argument functor: Hom_A(W, F(-)) ∘ G  ≡  Hom_A(W, (F∘G)(-)). // "accumulate the functor"
// Note: we express functor composition via `compose_morph_fapp0` in `Cat_cat` (not via `compose_functors`, which is defined later). // computational-friendly
rule @compose_morph_fapp0 Cat_cat $C $B Cat_cat (@hom_cov $A $W $B $F) $G
  ↪ @hom_cov $A $W $C (@compose_morph_fapp0 Cat_cat $C $B $A $F $G);

// Sanity: the above rewrite fires definitionally (conversion).                                        // exercise the rule
assert [A : Cat] [B : Cat] [C : Cat] (W : τ (Obj A))
  (F : τ (Obj (Functor B A))) (G : τ (Obj (Functor C B))) ⊢
  @compose_morph_fapp0 Cat_cat C B Cat_cat (@hom_cov A W B F) G
    ≡ @hom_cov A W C (@compose_morph_fapp0 Cat_cat C B A F G);


// -------------------------------------------------------------------------------------------------
// 7. Dependent categories (isofibrations / fibrations)                                              // Cat-valued type families
// -------------------------------------------------------------------------------------------------

// `Catd A` is the type of “categories dependent on A” (a fibration over A).                         // a.k.a. displayed categories / fibrations
constant symbol Catd : Π (A : Cat), TYPE;                                                           // classifier of dependent categories over A

// Terminal dependent category over A (constant fibration with terminal fibres).                     // unit family / trivial fibration
constant symbol Terminal_catd : Π (A : Cat), Catd A;                                                 // terminal displayed category

// Grothendieck construction: a Cat-valued functor A → Cat_cat gives an isofibration over A.         // category of elements / ∫ construction
constant symbol IsoFibration_catd : Π [A : Cat], τ (Obj (Functor A Cat_cat)) → Catd A;               // ∫M : Catd(A) for M : A → Cat

/*
  Displayed/dependent functors: slice-style vs general base functor

  - In cartierSolution13.lp, a displayed functor can be "over an arbitrary base functor":
      funcd A F B   (A : catd X, B : catd Y, F : func X Y)
    so a displayed morphism remembers a base map F : X → Y.
    Composition then produces a displayed functor over the composite base map (F∘G).

  - In emdash3.lp we choose the *slice-style* presentation:
      Functord(F,E) where both displayed categories live over the same base B : Cat.
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

// `Functord A B` is the category of dependent functors (sections / displayed functors).             // Π-type / dependent function space
// Intuition: if E : Catd(B) is a family over B and F is the “shape”, then Functord(F,E) is Π-sections. // categorical dependent product
constant symbol Functord : Π [B : Cat], Π (F : Catd B), Π (E : Catd B), Cat;                         // Functord(F,E) : Cat

// Dependent identity functor (identity section).                                                    // id in the Π-category
constant symbol identity_functord [Z : Cat] [A:Catd Z] : τ (Obj (Functord A A));                     // id : Obj(Functord(A,A))

// Dependent composition of dependent functors.                                                      // composition in Π-category
symbol compose_functorsd [Z : Cat] [A:Catd Z] [B:Catd Z] [C:Catd Z]                                  // base Z and displayed categories A,B,C
  (F: τ (Obj (Functord B C))) (G: τ (Obj (Functord A B))) : τ (Obj (Functord A C));                 // compose : (B→C) × (A→B) → (A→C)

// Fibre of a dependent category E over x:B (displayed category at a base object).                   // E(x) in type theory
injective symbol Fibre_cat : Π [B : Cat] (E : Catd B) (xB : τ (Obj B)), Cat;                         // fibre category at xB

// Fibre of a Grothendieck construction is the original value (strictly, on objects).                // ∫M fibre at x is M(x)
rule Fibre_cat (IsoFibration_catd $M) $x ↪ fapp0 $M $x;                                              // fibre(∫M,x) ↪ M(x)

// Special case: fibre of ∫(Hom(X, F-)) is the hom-category Hom(X, F(x)).                             // representable fibration
rule Fibre_cat (IsoFibration_catd (hom_cov $X $F)) $xZ ↪ Hom $X (fapp0 $F $xZ);                       // fibre(∫Hom(X,F-),x) ↪ Hom(X,Fx)

// Pullback of a dependent category along a functor (reindexing/substitution).                       // substitution / base change
symbol Pullback_catd : Π [A : Cat] [B : Cat], Catd B → τ (Obj (Functor A B)) → Catd A;               // F^*E : Catd(A)
rule Fibre_cat (Pullback_catd $E $F) $xA ↪ Fibre_cat $E (fapp0 $F $xA);                              // fibre(F^*E,x) ↪ fibre(E,Fx)

// Pullback of an isofibration (Grothendieck construction) is isofibration of the precomposition.    // ∫(E∘F) ≅ F^*(∫E)
// Here `E : B → Cat_cat` and `F : A → B`, and we express `E∘F` via composition in `Cat_cat`.         // avoids relying on later `compose_functors`
// This is the key bridge for “general base functor” displayed maps: reindex first, then use Functord. // simulate funcd-over-F
rule @Pullback_catd $A $B (@IsoFibration_catd $B $E) $F
  ↪ @IsoFibration_catd $A (@compose_morph_fapp0 Cat_cat $A $B Cat_cat $E $F);

// -------------------------------------------------------------------------------------------------
// 8. Natural transformations (2-cells) as morphisms in functor categories                            // transfors
// -------------------------------------------------------------------------------------------------

// `Transf(F,G)` is the category of natural transformations between F and G (and higher cells).      // 2-cells (and beyond)
constant symbol Transf : Π [A : Cat], Π [B : Cat], Π (F : τ (Obj (Functor A B))), Π (G : τ (Obj (Functor A B))), Cat; // Transf(F,G) : Cat

/*
  tapp_func (outer component / “superscript” viewpoint)

  Caution about notation: the binder `X : Obj(A)` here is an *external* projection index, not the usual
  “subscript object” of a natural transformation component.

  - Usual 1-categorical notation: for ϵ : Nat(F,G) and Y : Obj(A), we write ϵ_Y : Hom(FY, GY).
    In our encoding, that *inner* index (Y) lives inside the representable `Hom_A(X,-)` and is not the
    explicit binder of `tapp_func`.

  - Here `X` is better thought of as a superscript: ϵ ↦ ϵ^X, a map that takes a transformation ϵ and
    returns a dependent functor between representables:
      ϵ^X : Hom_A(X,-)  ⇒  Hom_B(FX, G(-)).
    The “subscript” can then be either:
      * an object Y (identity arrow), giving a component ϵ^X_Y,
      * or more generally an arrow f : Y₁ → Y₂, giving ϵ^X_f (naturality along f).

  - In the strict (non-lax) 1-categorical case, the familiar equation is:
      ϵ_{Y₂} ∘ F(f)  =  G(f) ∘ ϵ_{Y₁}.
    This is what “2-cell data” should satisfy; in the ω-setting it iterates inside hom-categories.

  Why package this as a functor (Transf F G → Functord(...))?
  - A modification α : ϵ ⇒ ϵ' (a 3-cell) has components expressed in terms of transformations, so after
    fixing the external index X, the source/target (ϵ, ϵ') become *functor-like* data (`tapp_fapp0 X ϵ`),
    letting us iterate: modifications → transformations between those component-functors → higher cells.
  - Extreme visualization: if A is Terminal_cat (only one X), then “projecting at X” is trivial and
    tapp becomes close to the idea that a natural transformation can be presented as a functorial object.
*/
symbol tapp_func : Π [A : Cat], Π [B : Cat], Π [F G : τ (Obj (Functor A B))],                             // domain/codomain categories and functors F,G
  Π (X: τ (Obj A)),                                                                                   // component at object X
  τ (Obj (Functor (Transf F G)
         (Functord (IsoFibration_catd (hom_cov X (@identity_functor A)))                              // source: Hom(X,-) over A (identity)
                  (IsoFibration_catd (hom_cov (fapp0 F X) G)))));                                     // target: Hom(FX, G(-)) over A

// `tapp_fapp0` is the fapp0 part of `tapp_func`
symbol tapp_fapp0 : Π [A : Cat], Π [B : Cat], Π [F G : τ (Obj (Functor A B))],                             // domain/codomain categories and functors F,G
  Π (X: τ (Obj A)), Π (ϵ : τ (Obj (Transf F G))),                                                    // transformation ϵ and object X
  τ (Obj (Functord (IsoFibration_catd (hom_cov X (@identity_functor A)))                              // source: Hom(X,-) over A (identity)
                  (IsoFibration_catd (hom_cov (fapp0 F X) G))));                                     // target: Hom(FX, G(-)) over A

// β-rule: `tapp_fapp0` is definitionally the object-action of the functor `tapp_func`.               // unpack tapp_func at objects
rule fapp0 (@tapp_func $A $B $F $G $X) $ϵ ↪ @tapp_fapp0 $A $B $F $G $X $ϵ;

// Key identification: the hom-category of the functor-category is the transformation-category.      // Hom_{Functor(A,B)}(F,G) ≅ Transf(F,G)
rule @Hom (Functor _ _) $F $G ↪ Transf $F $G;                                                        // definitional equality of homs


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
symbol Total_cat [A : Cat] (M: Catd A) : Cat;                                                        // ∫M : Cat

// Projection π₁ : Total_cat(M) → A (the “base” projection).                                          // comprehension projection
injective symbol Total_cat_proj [A : Cat] (M: Catd A) : τ (Obj (Functor (Total_cat M) A));           // functor object in Functor(∫M, A)

// Dependent projection π₂ as a dependent functor into the pulled-back family over ∫M.               // second projection (displayed)
injective symbol Total_cat_projd [A : Cat] (M: Catd A) :                                             // dependent object: section over ∫M
  τ (Obj (Functord (Terminal_catd (Total_cat M)) (Pullback_catd M (Total_cat_proj M))));            // π₂ : 1_{∫M} ⇒ (π₁)^*M

injective symbol Total_cat_intro_func : Π [X : Cat] [A : Catd X] [B : Catd X],
τ (Obj (Functord A B)) → τ (Obj (Functor (Total_cat A) (Total_cat B)));

// Terminal displayed functor into the terminal family (slice-style).                                 // unique map A → 1_X in Catd(X)
injective symbol Terminal_functord : Π [X : Cat] (A : Catd X), τ (Obj (Functord A (Terminal_catd X)));

// Terminal comprehension laws (cartierSolution13: Context_cat/Context_elimCat/Context_intro).        // ∫(1_X) ≡ X, π₁ ≡ id
rule Total_cat (Terminal_catd $A) ↪ $A;                                                               // ∫(1_A) ↪ A
rule Total_cat_proj (Terminal_catd $A) ↪ @identity_functor $A;                                        // π₁ : ∫(1_A)→A ↪ id_A

// Pullback preserves terminal displayed categories.                                                  // F^*(1_B) ≡ 1_A
rule @Pullback_catd $A $B (Terminal_catd $B) $F ↪ Terminal_catd $A;

// The dependent projection π₂ is the identity section when M is terminal.                            // π₂ : 1_{∫1} ⇒ (π₁)^*1  ↪ id
rule Total_cat_projd (Terminal_catd $A) ↪ @identity_functord $A (Terminal_catd $A);

// Intro rules: functor between totals induced by a displayed functor in the slice.                   // Context_intro_func analogues
rule @Total_cat_intro_func $X $A $A (@identity_functord $X $A) ↪ @identity_functor (Total_cat $A);     // ∫id ↪ id
rule @Total_cat_intro_func $X $A (Terminal_catd $X) (Terminal_functord $A) ↪ Total_cat_proj $A;        // ∫(!) ↪ π₁

// β-like law: composing the induced functor with the projection of B gives the projection of A.      // (∫FF);π₁_B = π₁_A
rule @compose_morph_fapp0 Cat_cat (Total_cat $A) (Total_cat $B) $X (Total_cat_proj $B) (@Total_cat_intro_func $X $A $B $FF)
  ↪ Total_cat_proj $A;

// TODO: Review this claim: such additional rewrite rules are for convenience:
// Objects of ∫M are Σ (x : Obj(A)), Obj(fibre(M,x)).                                                 // Σ-object description of total objects
rule τ (Obj (Total_cat $M)) ↪ `τΣ_ X : τ (Obj _), Obj (Fibre_cat $M X);                               // τ Obj(∫M) ↪ Σ x:A, Obj(M(x))

// -------------------------------------------------------------------------------------------------
// 11. Opposite category (involution)                                                                 // A ↦ Aᵒᵖ
// -------------------------------------------------------------------------------------------------

injective symbol Op_cat : Cat → Cat;                                                                 // opposite category operation
rule Op_cat (Op_cat $A) ↪ $A;                     
                                                   // involutive law: (Aᵒᵖ)ᵒᵖ ≡ A
injective symbol Op_catd : Π [X : Cat] (A : Catd X), Catd (Op_cat X);
rule Op_catd (Op_catd $A) ↪ $A;                     

// -------------------------------------------------------------------------------------------------
// 12. Terminal category and “constant functors from the terminal”                                   // 1 and points as functors
// -------------------------------------------------------------------------------------------------

// The terminal category 1 (one object, one morphism).                                                // categorical unit
constant symbol Terminal_cat : Cat;                                                                  // 1 : Cat

// The unique functor A → 1 (terminal functor).                                                       // ! : A → 1
injective symbol Terminal_func : Π (A : Cat), τ (Obj (Functor A Terminal_cat));                      // object of Functor(A,1)

// Distinguished object * : Obj(1) (everything is definitionally equal to it via rules if desired).  // point of the terminal category
constant symbol Terminal_obj : τ (Obj Terminal_cat);                                                 // * : Obj(1)

// “Object as functor”: an object y:Obj(Y) induces a functor 1 → Y selecting y.                       // points as functors
injective symbol Obj_func : Π [Y : Cat], τ (Obj Y) → τ (Obj (Functor Terminal_cat Y));               // y ↦ (1→Y) picking y

// Computation: applying the point-functor to the unique object of 1 yields the point.                // evaluation at *
rule fapp0 (Obj_func $F) $M ↪ $F;                                                                    // (const F)(*) ↪ F (for any * in 1)


// -------------------------------------------------------------------------------------------------
// 13. Binary products of categories                                                                  // A×B
// -------------------------------------------------------------------------------------------------

// Product of categories (binary product in Cat).                                                     // categorical product
injective symbol Product_cat : Π (A1 : Cat) (A2 : Cat), Cat;                                         // A1 × A2 : Cat

// Functorial projections (as functors out of any B): precomposition with π₁, π₂.                     // (−)∘πᵢ on functor categories
symbol Product_projL_func : Π [A1 A2 B: Cat], τ (Obj (Functor B (Product_cat A1 A2))) →               // given H : B → (A1×A2)
  τ (Obj (Functor B A1));                                                                            // obtain π₁∘H : B → A1
symbol Product_projR_func : Π [A1 A2 B: Cat], τ (Obj (Functor B (Product_cat A1 A2))) →               // given H : B → (A1×A2)
  τ (Obj (Functor B A2));                                                                            // obtain π₂∘H : B → A2

// Pairing of functors: given F:B→A1 and G:B→A2, build ⟨F,G⟩:B→A1×A2.                                 // universal property at functor level
injective symbol Product_pair_func : Π [A1 A2 I : Cat] (F : τ (Obj (Functor I A1))) (G : τ (Obj (Functor I A2))), // inputs functors
  τ (Obj (Functor I (Product_cat A1 A2)));                                                           // paired functor to product

// Object-level projections/pairing (objects of A1×A2 are pairs).                                     // components of product objects
symbol Product_projL : Π [A1 A2 : Cat], τ (Obj (Product_cat A1 A2)) → τ (Obj A1);                     // π₁ on objects
symbol Product_projR : Π [A1 A2 : Cat], τ (Obj (Product_cat A1 A2)) → τ (Obj A2);                     // π₂ on objects
injective symbol Product_pair : Π [A1 A2 : Cat] (X : τ (Obj A1)) (Y : τ (Obj A2)),                    // constructor on objects
  τ (Obj (Product_cat A1 A2));                                                                       // ⟨X,Y⟩ : Obj(A1×A2)

// Compatibility between Obj_func (points) and product structure (pointwise pairing/projections).     // evaluation coherence
rule Product_pair_func (Obj_func $X) (Obj_func $Y) ↪ Obj_func (Product_pair $X $Y);                  // ⟨x,y⟩ as functor from 1
rule Product_projL_func (Obj_func $XY) ↪ Obj_func (Product_projL $XY);                               // π₁ on points-as-functors
rule Product_projR_func (Obj_func $XY) ↪ Obj_func (Product_projR $XY);                               // π₂ on points-as-functors

// -------------------------------------------------------------------------------------------------
// 14. Fibrewise products (products of displayed categories)                                         // displayed/product fibrations
// -------------------------------------------------------------------------------------------------

// Product of dependent categories over the same base Z (fibrewise product).                          // displayed product
injective symbol Product_catd : Π [Z : Cat] (U : Catd Z) (A : Catd Z), Catd Z;                       // U×A : Catd(Z)
rule Fibre_cat (Product_catd $U $A) $xZ ↪ Product_cat (Fibre_cat $U $xZ) (Fibre_cat $A $xZ);         // fibre(U×A,x) ↪ fibre(U,x)×fibre(A,x)

// Displayed projections/pairing (dependent functors witnessing product structure).                   // displayed πᵢ and pairing
symbol Product_projL_functord : Π [Z : Cat] [U A : Catd Z], τ (Obj (Functord (Product_catd U A) U));  // π₁ : U×A → U
symbol Product_projR_functord : Π [Z : Cat] [U A : Catd Z], τ (Obj (Functord (Product_catd U A) A));  // π₂ : U×A → A
injective symbol Product_pair_functord : Π [Z : Cat] [U A B : Catd Z]                                 // pairing in displayed world
  (F : τ (Obj (Functord B U))) (G : τ (Obj (Functord B A))),                                         // sections into U and A
  τ (Obj (Functord B (Product_catd U A)));                                                           // paired section into U×A

// -------------------------------------------------------------------------------------------------
// 15. Composition as a functor (uncurried / product form)                                           // internal composition map
// -------------------------------------------------------------------------------------------------

// The “composition morphism” as a functor out of a product of hom-categories.                        // functorial / internal
// Think: this is the cartierSolution13-style "parametric object in a context", but now in ω-form:
// it packages the entire operation as an object in a functor-category, so it can itself have higher structure.
symbol compose_morph : Π [A : Cat], Π [X: τ (Obj A)], Π [Y: τ (Obj A)], Π [Z: τ (Obj A)],            // ambient A and objects
  τ (Obj (Functor (Product_cat (Hom Y Z) (Hom X Y)) (Hom X Z)));                                      // an object in the functor-category

// Computation: applying the composition functor to a pair (g,f) returns the composite g∘f.           // β-rule for composition functor
rule (fapp0 (@compose_morph $A $X $Y $Z)) (Product_pair $g $f) ↪ @compose_morph_fapp0 $A $X $Y $Z $g $f; // compose(g,f) ↪ g∘f

// Sanity check: the β-rule is visible at the level of definitional equality / conversion.            // exercise the rule
assert [A : Cat] [X : τ (Obj A)] [Y : τ (Obj A)] [Z : τ (Obj A)]
  (g : τ (Obj (Hom Y Z))) (f : τ (Obj (Hom X Y))) ⊢
  fapp0 (@compose_morph A X Y Z) (Product_pair g f) ≡ @compose_morph_fapp0 A X Y Z g f;

// Composition of functors is composition in Cat_cat (a special case of compose_morph_fapp0).         // categorical composition in Cat
symbol compose_functors [A:Cat] [B:Cat] [C:Cat]                                                       // A,B,C : Cat
  (F: τ (Obj (Functor B C))) (G: τ (Obj (Functor A B))) : τ (Obj (Functor A C))                      // F∘G : Functor(A,C)
≔ @compose_morph_fapp0 Cat_cat _ _ _ F G;                                                             // compose in Cat_cat

// -------------------------------------------------------------------------------------------------
// 16. Draft: “simplicial” view on higher morphisms via slice-like dependent functors                // experiments / TODO zone
// -------------------------------------------------------------------------------------------------

// TODO: implement contravariant hom (`hom_con`) and opposites coherently (requires Op_cat functoriality). // dual Yoneda
// TODO: add explicit “globular” source/target operations and interchange/composition laws.          // ω-category axioms
// TODO: connect with Kosta Došen's “stacking” (horizontal composition of 2-cells along a 1-cell).   // 2-simplex / 3-simplex diagrams

// Dependent Yoneda/hom for a dependent category: “Hom in the fibre / in a slice”.                   // placeholder (signature likely evolves)
constant symbol homd_cov : Π [Z : Cat], Π [A : Catd Z], Π [W_: τ (Obj Z)]                             // base Z, displayed A, base object W_
  (W : τ (Obj (Fibre_cat A W_))), Π [B : Catd Z], Π (F : τ (Obj (Functord B A))),                    // W in fibre, B another displayed cat, F : B→A
  τ (Obj (Functor (Total_cat (Product_catd B (IsoFibration_catd (hom_cov W_ (@identity_functor Z))))) // source category (a total category)
                Cat_cat));                                                                            // target category Cat_cat (Cat-valued functors)

// Application of a dependent functor on objects, fibrewise.                                         // fibred fapp0
symbol dfapp0 : Π [Z : Cat], Π [A : Catd Z], Π [B : Catd Z], Π (F : τ (Obj (Functord A B))),          // dependent functor F : A→B
  Π [xZ : τ (Obj Z)], τ (Obj (Fibre_cat A xZ)) → τ (Obj (Fibre_cat B xZ));                            // map objects in each fibre

// “Slice-category” / simplicial action: fapp1d packages fapp1 as a dependent functor over representables. // 2-simplex intuition
// Motivation: complements the globular iteration (Hom(X,Y) : Cat) with a simplicial iteration (fibrewise). // 2- and 3-simplex pictures
symbol fapp1d : Π [A : Cat], Π [B : Cat], Π (F : τ (Obj (Functor A B))), Π [X: τ (Obj A)],             // functor F and object X
  τ (Obj (Functord (IsoFibration_catd (hom_cov X (@identity_functor A)))                               // source displayed: Hom(X,-)
                  (IsoFibration_catd (hom_cov (fapp0 F X) F))));                                       // target displayed: Hom(FX, F-)

// Link: the object-action dfapp0 of fapp1d reduces to applying fapp1 on a morphism-object.           // coherence rule between globular & simplicial views
rule dfapp0 (@fapp1d $A $B $F $X) $f ↪ fapp0 (@fapp1 _ _ $F _ _) $f;                                  // dfapp0(fapp1d(F,X),f) ↪ fapp0(fapp1(F,_,_),f)

// Application of a dependent functor on morphisms (still draft: depends on `homd_cov`).              // fibred fapp1
symbol dfapp1d : Π [Z : Cat], Π [A : Catd Z], Π [B : Catd Z], Π (F : τ (Obj (Functord A B))),          // dependent functor F : A→B
  Π [X_: τ (Obj Z)] (X: τ (Obj (Fibre_cat A X_))),                                                    // base object X_ and fibre object X
  τ (Obj (Functord (IsoFibration_catd (homd_cov X (@identity_functord _ A)))                            // source hom in fibre (placeholder)
                  (IsoFibration_catd (homd_cov (dfapp0 F X) F))));                                     // target hom in fibre (placeholder)

// Dependent transformations between dependent functors (displayed natural transformations).          // displayed transfors
constant symbol dTransf : Π [Z : Cat], Π [A : Catd Z], Π [B : Catd Z],                                 // base and displayed categories
  Π (F : τ (Obj (Functord A B))), Π (G : τ (Obj (Functord A B))), Cat;                                 // dTransf(F,G) : Cat

/*
  dtapp_func is the displayed analogue of tapp_func.

  Again, the binders (X_, X) are *external* projection indices:
  - X_ : Obj(Z) picks a fibre of the displayed category A : Catd(Z),
  - X : Obj(Fibre_cat A X_) is the point *inside that fibre* at which we project components.

  Think “superscripted component”: for ϵ : dTransf(F,G), we get ϵ^(X_,X) as a dependent functor between
  displayed representables. This is the step that makes iteration possible:
  modifications between displayed transfors project to transfors between these component-functors, etc.
*/
symbol dtapp_func : Π [Z : Cat], Π [A : Catd Z], Π [B : Catd Z], Π [F G : τ (Obj (Functord A B))],          // dependent functors F,G
Π (X_: τ (Obj Z)) (X: τ (Obj (Fibre_cat A X_))),                                                      // component at fibre object X
   τ (Obj (Functor (dTransf F G)
          (Functord (IsoFibration_catd (homd_cov X (@identity_functord _ A)))                            // source hom (placeholder)
                    (IsoFibration_catd (homd_cov (dfapp0 F X) G)))));                                     // target hom (placeholder)

// `dtapp_fapp0` is the fapp0 part of `dtapp_func`
symbol dtapp_fapp0 : Π [Z : Cat], Π [A : Catd Z], Π [B : Catd Z], Π [F G : τ (Obj (Functord A B))],          // dependent functors F,G
Π (X_: τ (Obj Z)) (X: τ (Obj (Fibre_cat A X_))),                                                      // component at fibre object X
  Π (ϵ : τ (Obj (dTransf F G))), 
  τ (Obj (Functord (IsoFibration_catd (homd_cov X (@identity_functord _ A)))                            // source hom (placeholder)
                  (IsoFibration_catd (homd_cov (dfapp0 F X) G))));                                     // target hom (placeholder)

// β-rule: `dtapp_fapp0` is definitionally the object-action of the functor `dtapp_func`.             // unpack dtapp_func at objects
rule fapp0 (@dtapp_func $Z $A $B $F $G $X_ $X) $ϵ ↪ @dtapp_fapp0 $Z $A $B $F $G $X_ $X $ϵ;

// Key identification: the hom-category of the functor-category is the transformation-category.      // Hom_{Functor(A,B)}(F,G) ≅ Transf(F,G)
rule @Hom (Functord _ _) $F $G ↪ dTransf $F $G;                                                        // definitional equality of homs

// The action of a displayed (2-)transformation on a displayed (3-)modification: fapp1-part of `dtapp_func`. // displayed “components of components”
symbol dtapp_fapp1 : Π [Z : Cat], Π [A : Catd Z], Π [B : Catd Z], Π [F G : τ (Obj (Functord A B))],        // base+displayed cats and functors
  Π (X_ : τ (Obj Z)) (X : τ (Obj (Fibre_cat A X_))),                                                     // component index (in a fibre)
  Π [ϵ : τ (Obj (dTransf F G))], Π [ϵ' : τ (Obj (dTransf F G))],                                         // displayed transfors ϵ ⇒ ϵ'
  τ (Obj (Functor (@Hom (dTransf F G) ϵ ϵ')                                                              // displayed modifications between ϵ and ϵ'
                 (dTransf (dtapp_fapp0 X_ X ϵ) (dtapp_fapp0 X_ X ϵ'))));                                  // displayed transfors between components

// β-rule: `dtapp_fapp1` is definitionally the hom-action of the functor `dtapp_func`.                // unpack dtapp_func at homs
rule @fapp1 _ _ (@dtapp_func $Z $A $B $F $G $X_ $X) $ϵ $ϵ'
  ↪ @dtapp_fapp1 $Z $A $B $F $G $X_ $X $ϵ $ϵ';

// The action of a (2-)transformation on a (3-)modification: fapp1-part of `tapp_func`.               // “components of components”
// If α : Hom_{Transf(F,G)}(ϵ,ϵ') is a modification, then `tapp_fapp1 X ϵ ϵ'` transports α to a        // functoriality of component-evaluation
// dependent transformation between the dependent functors `tapp_fapp0 X ϵ` and `tapp_fapp0 X ϵ'`.     // (codomain hom is dTransf by the rule above)
symbol tapp_fapp1 : Π [A : Cat], Π [B : Cat], Π [F G : τ (Obj (Functor A B))],                          // base categories and functors F,G
  Π (X : τ (Obj A)),                                                                                   // component index X
  Π [ϵ : τ (Obj (Transf F G))], Π [ϵ' : τ (Obj (Transf F G))],                                         // transformations ϵ ⇒ ϵ'
  τ (Obj (Functor (@Hom (Transf F G) ϵ ϵ')                                                            // modifications between ϵ and ϵ'
                 (dTransf (tapp_fapp0 X ϵ) (tapp_fapp0 X ϵ'))));                                       // dependent transf between components

// β-rule: `tapp_fapp1` is definitionally the hom-action of the functor `tapp_func`.                  // unpack tapp_func at homs
rule @fapp1 _ _ (@tapp_func $A $B $F $G $X) $ϵ $ϵ'
  ↪ @tapp_fapp1 $A $B $F $G $X $ϵ $ϵ';



// -------------------------------------------------------------------------------------------------
// 17. Sanity checks (lightweight “unit tests” for rewrite normalization)                             // keep small, avoids proof noise
// -------------------------------------------------------------------------------------------------

// Op_cat involution reduces by rewriting.                                                            // checks Op_cat rule fires
assert ⊢ Op_cat (Op_cat Cat_cat) ≡ Cat_cat;                                                          // (Cat_catᵒᵖ)ᵒᵖ ≡ Cat_cat

// Identity functor on objects reduces by rewriting.                                                  // checks fapp0(identity_functor) β-rule
compute fapp0 (@identity_morph Cat_cat Terminal_cat) Terminal_obj;                                    // normal form should be `Terminal_obj`

// tapp_func object-action reduces to tapp_fapp0 by rewriting.                                         // checks tapp β-rule fires
assert [A : Cat] [B : Cat] [F G : τ (Obj (Functor A B))] (X : τ (Obj A)) (ϵ : τ (Obj (Transf F G))) ⊢
  fapp0 (tapp_func X) ϵ ≡ tapp_fapp0 X ϵ;

// dtapp_func object-action reduces to dtapp_fapp0 by rewriting.                                       // checks dtapp β-rule fires
assert [Z : Cat] [A : Catd Z] [B : Catd Z] [F G : τ (Obj (Functord A B))]
  (X_ : τ (Obj Z)) (X : τ (Obj (Fibre_cat A X_))) (ϵ : τ (Obj (dTransf F G))) ⊢
  fapp0 (dtapp_func X_ X) ϵ ≡ dtapp_fapp0 X_ X ϵ;

// tapp_func hom-action reduces to tapp_fapp1 by rewriting (uses @Hom(Functord..) ≡ dTransf).         // checks tapp fapp1 β-rule fires
assert [A : Cat] [B : Cat] [F G : τ (Obj (Functor A B))] (X : τ (Obj A))
  (ϵ : τ (Obj (Transf F G))) (ϵ' : τ (Obj (Transf F G))) ⊢
  @fapp1 _ _ (tapp_func X) ϵ ϵ' ≡ @tapp_fapp1 A B F G X ϵ ϵ';

// dtapp_func hom-action reduces to dtapp_fapp1 by rewriting.                                         // checks dtapp fapp1 β-rule fires
assert [Z : Cat] [A : Catd Z] [B : Catd Z] [F G : τ (Obj (Functord A B))]
  (X_ : τ (Obj Z)) (X : τ (Obj (Fibre_cat A X_)))
  (ϵ : τ (Obj (dTransf F G))) (ϵ' : τ (Obj (dTransf F G))) ⊢
  @fapp1 _ _ (dtapp_func X_ X) ϵ ϵ' ≡ @dtapp_fapp1 Z A B F G X_ X ϵ ϵ';

// Pullback of a Grothendieck isofibration reduces to Grothendieck of precomposition.                 // checks Pullback_catd/∫ rewrite fires
assert [A : Cat] [B : Cat] (E : τ (Obj (Functor B Cat_cat))) (F : τ (Obj (Functor A B))) ⊢
  @Pullback_catd A B (@IsoFibration_catd B E) F
    ≡ @IsoFibration_catd A (@compose_morph_fapp0 Cat_cat A B Cat_cat E F);
