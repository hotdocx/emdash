/*
  m— / emdash2
  Functorial programming for (strict/lax) ω-categories in Lambdapi.
*/

flag "eta_equality" on;

// `TYPE` is lambdapi-framework (meta-) type for collections;
// so in the object-lamguage, i.e. emdah, any `ABC : TYPE` means that `ABC` is a collection/grammar-entity to collect/classify some things
// A minimal `Grpd : TYPE` + decoding function `τ : Grpd → TYPE`,
// `Grpd` (often written `Set` in the Lambdapi doc) is the (meta-)collection of ω-groupoid (or "sets" for ease of understanding), similar as in hott homotopy type theory.
constant symbol Grpd : TYPE;
injective symbol τ : Grpd → TYPE;
builtin "T" ≔ τ;
builtin "Prop" ≔ Grpd;
builtin "P" ≔ τ;

constant symbol = : Π [a: Grpd], τ a → τ a → Grpd; /* here `=` ends in `Grpd` ω-groupoid instead of the usual `Prop` (the `Set` in the Lambdapi doc uses a `=` which lands in `Prop`) */
notation = infix 10;

constant symbol eq_refl : Π [a: Grpd], Π x: τ a, τ (x = x);
symbol ind_eq : Π [a: Grpd], Π [x: τ a], Π [y: τ a], τ (x = y) → Π p: (τ a → Grpd), τ (p y) → τ (p x);
rule ind_eq (eq_refl $x) $p $u ↪ $u;
builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ ind_eq;

// A tiny inhabited type, useful for “always-true” unification-rule conditions.
// unif_rule A $x ≡ B $x ↪ [ tt ≡ tt ]
inductive unit : TYPE ≔ | tt : unit;

// Minimal naturals (dimension index).
inductive Nat : TYPE ≔
| Z : Nat
| S : Nat → Nat;

// # --- Categories ---

// `Cat` is the collection of categories
constant symbol Cat : TYPE;

// `Obj` is the underlying/core groupoid of a category
injective symbol Obj : Cat → Grpd;

// `Hom` is the category of morphisms of a (omega-)category
injective symbol Hom : Π [A : Cat] (X:  τ (Obj A)) (Y: τ (Obj A)), Cat;

// notation: id
// `identity_morph` is the identity in categories
injective symbol identity_morph : Π[A : Cat], Π(X: τ (Obj A)), τ (Obj (Hom X X));


// # --- Functors ---

// `Functor` is the category of functors between categories
constant symbol Functor : Π(A : Cat), Π(B : Cat), Cat;

// `fapp0` is the application of a functor to an object
symbol fapp0 : Π[A : Cat], Π[B : Cat], Π(F : τ (Obj (Functor A B))), τ (Obj A) → τ (Obj B);
// `fapp1` is the application of a functor to a morphism
symbol fapp1 : Π[A : Cat], Π[B : Cat], Π(F : τ (Obj (Functor A B))),
  Π[X: τ (Obj A)], Π[Y: τ (Obj A)], τ (Obj (Functor (Hom X Y) (Hom (fapp0 F X) (fapp0 F Y))));

// # --- Grpd_cat category classifier, discrete fibrations, yoneda representable Functor ---

// `Grpd_cat` is the category of types/sets/groupoids,
// classifier for discrete modules/fibrations; where a discrete fibration is a functor in `Functor (A, Grpd_cat)`
constant symbol Grpd_cat : Cat;

unif_rule τ (Obj $A) ≡ Grpd ↪ [ $A ≡ Grpd_cat ];

// see below section "extensionality for Grpd_cat" for structure-preservation
rule τ (Obj (@Hom Grpd_cat $X $Y)) ↪ (τ $X → τ $Y);

// # --- Cat category classifier, fibrations, isofibrations, yoneda representable Functor ---

// `Cat_cat` is the category of categories, classifier for non-discrete fibrations; 
// where a non-discreate fibration is a functor in `Functor (A, Cat_cat)`
constant symbol Cat_cat : Cat;

unif_rule τ (Obj $A) ≡ Cat ↪ [ $A ≡ Cat_cat ];

// arrows in `Cat_cat` are functors (precisely: the Hom-category of the category of categories is same as the Functor category)
rule @Hom Cat_cat $X $Y ↪ Functor $X $Y;

// `identity_functor` is the identity functor
// this can and will be defined in terms of `identity_morph` of Cat_cat
constant symbol identity_functor [A:Cat]: τ ( Obj (Functor A A));

// yoneda covarient embedding functor to Cat_cat; also TODO: contravariant Yoneda
// so `hom_cov W F` (which is a functor in `Functor (A, Cat_cat)`)  is the usual-notations `Hom_A(W, F -)` 
// that is Hom precomposed with F at the covariant argument
constant symbol hom_cov : Π [A : Cat], Π (W: τ (Obj A)), Π [B : Cat], Π (F : τ (Obj (Functor B A))), τ (Obj (Functor B Cat_cat));

rule fapp0 (hom_cov $X $F) $Y ↪ Hom $X (fapp0 $F $Y);


// # --- Dependent categories (isofibrations) ---

// isofibration E: Catd A has semantics : a functor E -> A that is Functor(E, A).
constant symbol Catd : Π(A : Cat), TYPE;

constant symbol identity_Catd : Π(A : Cat), Catd A;



// `Fibre E xB` is the fibre of the fibration E at xB : B
symbol Fibre : Π[B : Cat] (E : Catd B) (xB : τ (Obj B)), Cat;

// `Functord F E ` is a dependent functor, which is a section of E (of shape F);
// so it is the usual Pi-Product Π in the context of proof assistants:
// so if F was B (identity fibration), then `Functord F E` is `Π(xB : B) E(xB)`
constant symbol Functord : Π(B : Cat), Π(F : Catd B), Π(E : Catd B), Catd B;

// # --- Natural Transformations ---

// `Transf` is the category of natural transformations between functors
constant symbol Transf : Π [A : Cat], Π [B : Cat], Π (F : τ (Obj (Functor A B))), Π (G : τ (Obj (Functor A B))), Cat;

// Technical Goal:
// To iterate `Transf` so to get omega-categories, we need to "see"/reinterpret a natural transformation somehow as a functor...

// // notation:  (ϵ)._X  for  tapp ϵ X
// symbol tapp : Π [A : Cat], Π [B : Cat], Π [F G : τ (Obj (Functor A B))],
//   Π (ϵ : τ (Obj (Transf F G))), Π (X: τ (Obj A)), 
//   τ (Obj (Transf (hom_cov X (@identity_functor A)) (hom_cov (fapp0 F X) G)));
