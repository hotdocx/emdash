/*
  m— / emdash2
  Functorial programming for (strict/lax) ω-categories in Lambdapi.
*/

flag "eta_equality" on;

// A minimal Grpd : TYPE” + decoding function `τ : Grpd → TYPE`,
// mirroring the setup in `emdash.lp` so we can internalize “sets/groupoids of terms”.
constant symbol Grpd : TYPE;
injective symbol τ : Grpd → TYPE;
builtin "T" ≔ τ;
builtin "Prop" ≔ Grpd;
builtin "P" ≔ τ;

constant symbol = : Π [a: Grpd], τ a → τ a → Grpd; /* ω-groupoid vs Prop */
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

constant symbol Cat : TYPE;

injective symbol Obj : Cat → Grpd;

injective symbol Hom : Π [A : Cat] (X:  τ (Obj A)) (Y: τ (Obj A)), Cat;


// # --- Functors ---

constant symbol Functor : Π(A : Cat), Π(B : Cat), Cat;

symbol fapp0 : Π[A : Cat], Π[B : Cat], Π(F : τ (Obj (Functor A B))), τ (Obj A) → τ (Obj B);
symbol fapp1 : Π[A : Cat], Π[B : Cat], Π(F : τ (Obj (Functor A B))),
  Π[X: τ (Obj A)], Π[Y: τ (Obj A)], τ (Obj (Functor (Hom X Y) (Hom (fapp0 F X) (fapp0 F Y))));

// # --- Grpd_cat category classifier, discrete fibrations, yoneda representable Functor ---

// category Grpd_cat of types/sets/groupoids, classifier for discrete modules/fibrations which become Functor (A, Grpd_cat)
// TODO: category Cat_cat of categories, classifier for non-discrete fibrations which become Functor (A, Cat_cat)
constant symbol Grpd_cat : Cat;

unif_rule τ (Obj $A) ≡ Grpd ↪ [ $A ≡ Grpd_cat ];

// see below section "extensionality for Grpd_cat" for structure-preservation
rule τ (Obj (@Hom Grpd_cat $X $Y)) ↪ (τ $X → τ $Y);

// # --- Cat category classifier, fibrations, isofibrations, yoneda representable Functor ---

constant symbol Cat_cat : Cat;

unif_rule τ (Obj $A) ≡ Cat ↪ [ $A ≡ Cat_cat ];

rule @Hom Cat_cat $X $Y ↪ Functor $X $Y;

// yoneda covarient embedding functor to Cat_cat; also TODO: contravariant Yoneda
constant symbol hom_cov : Π [A : Cat], Π (W: τ (Obj A)), Π [B : Cat], Π (F : τ (Obj (Functor B A))), τ (Obj (Functor B Cat_cat));

rule fapp0 (hom_cov $X $F) $Y ↪ Hom $X (fapp0 $F $Y);

// # --- Dependent categories ---

constant symbol Catd : Π(A : Cat), TYPE;

symbol Fibre : Π[B : Cat] (E : Catd B) (xB : τ (Obj B)), Cat;

constant symbol Functord : Π(B : Cat), Π(E : Catd B), Π(F : Catd B), Catd B;

// # --- Natural Transformations ---

constant symbol Transf : Π [A : Cat], Π [B : Cat], Π (F : τ (Obj (Functor A B))), Π (G : τ (Obj (Functor A B))), Cat;

constant symbol identity_functor [A:Cat]: τ ( Obj (Functor A A));

// // notation:  (ϵ)._X  for  tapp ϵ X
symbol tapp : Π [A : Cat], Π [B : Cat], Π [F G : τ (Obj (Functor A B))],
  Π (ϵ : τ (Obj (Transf F G))), Π (X: τ (Obj A)), 
  τ (Obj (Transf (hom_cov X (@identity_functor A)) (hom_cov (fapp0 F X) G)));
