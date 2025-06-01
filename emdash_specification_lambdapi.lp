/*
    m— emdash functorial programming
*/

// ===== START OF BASIC KERNEL SPECIFICATION  =====

flag "eta_equality" on;

constant symbol Type : TYPE;
injective symbol τ : Type → TYPE;
builtin "T" ≔ τ;
builtin "Prop" ≔ Type;
builtin "P" ≔ τ;

// only used for the trick to get Lambdapi unif_rule with empty conditions
// unif_rule A $x ≡ B $x ↪ [ tt ≡ tt ]
inductive unit : TYPE ≔ | tt : unit;


// # --- Categories ---

constant symbol Cat : TYPE;

injective symbol Obj : Cat → TYPE;

constant symbol Obj_Type : Cat → Type;
rule τ (Obj_Type $A) ↪ Obj $A;

injective symbol Hom : Π [A : Cat] (X: Obj A) (Y: Obj A), TYPE;

constant symbol Hom_Type : Π [A : Cat] (X: Obj A) (Y: Obj A), Type;
rule τ (@Hom_Type $A $X $Y) ↪ @Hom $A $X $Y;


// # --- Functors ---

constant symbol Functor : Π(A : Cat), Π(B : Cat), Cat;

symbol fapp0 : Π[A : Cat], Π[B : Cat], Π(F : Obj (Functor A B)), Obj A → Obj B;
symbol fapp1 : Π[A : Cat], Π[B : Cat], Π(F : Obj (Functor A B)),
  Π[X: Obj A], Π[Y: Obj A], Π(a: Hom X Y), Hom (fapp0 F X) (fapp0 F Y);

// ok these rules concerned `Obj (Functor A B)`, but what is `@Hom (Functor _ _)` ? answer:


// # --- Natural Transformations ---

constant symbol Transf : Π [A : Cat], Π [B : Cat], Π (F : Obj (Functor A B)), Π (G : Obj (Functor A B)), TYPE;

constant symbol Transf_Type : Π [A : Cat], Π [B : Cat], Π (F : Obj (Functor A B)), Π (G : Obj (Functor A B)), Type;
rule τ (@Transf_Type $A $B $F $G) ↪ @Transf $A $B $F $G;

// notation:  (ϵ)._X  for  tapp ϵ X
symbol tapp : Π [A : Cat], Π [B : Cat], Π [F : Obj (Functor A B)], Π [G : Obj (Functor A B)],
  Π (ϵ : Transf F G), Π (X: Obj A), Hom (fapp0 F X) (fapp0 G X);

// structure-preserving (components) expressed indirectly below, no explicit map required for this rule
rule @Hom (Functor _ _) $F $G ↪ Transf $F $G;


// # --- Set category classifier, discrete fibrations, yoneda representable Functor ---

// category Set of types/sets/groupoids, classifier for discrete modules/fibrations which become Functor (A, Set)
// TODO: category Cat_cat of categories, classifier for non-discrete fibrations which become Functor (A, Cat_cat)
constant symbol Set : Cat;

unif_rule Obj $A ≡ Type ↪ [ $A ≡ Set ];

// see below section "extensionality for Set" for structure-preservation
rule @Hom Set $X $Y ↪ (τ $X → τ $Y);

// yoneda covarient embedding functor to Set; also TODO: contravariant Yoneda
// this is a "fully-saturated" constructor `@hom_cov A W : Obj (Functor A Set)` inside kernel,
// unlike `compose_morph` which has a Π type
constant symbol hom_cov : Π [A : Cat], Π (W: Obj A), Obj (Functor A Set);
// constant symbol hom_con : Π [A : Cat], Π (W: Obj A), Obj (Functor Aᵒᵖ Set);

rule fapp0 (hom_cov $X) $Y ↪ Hom_Type $X $Y;

// # --- Cat category classifier, fibrations, isofibrations, yoneda representable Functor ---

constant symbol Cat_cat : Cat;

rule Obj Cat_cat ↪ Cat;
rule @Hom Cat_cat $X $Y ↪ Obj (Functor $X $Y);

constant symbol hom_cov_cat : Π [A : Cat], Π (W: Obj A), Obj (Functor A Cat_cat);

// the objects-map of hom_cov_cat is hom_cov
rule Obj (fapp0 (hom_cov_cat $W) $Y) ↪ Hom $W $Y;
rule fapp0 (fapp1 (hom_cov_cat $W) $a) $f ↪ (fapp1 (hom_cov $W) $a) $f;

// 2-morphim above 1-morphism  is  via hom_cov_cat and presence of classifier Cat_cat for fibrations
injective symbol Homd_ [A : Cat] [W: Obj A] [Y : Obj A] [Y': Obj A] (a: Hom Y Y') (f : Hom W Y) (h : Hom W Y') : TYPE
≔ @Hom (fapp0 (hom_cov_cat W) Y') (fapp0 (fapp1 (hom_cov_cat W) a) f) h;

// 2-element above 1-element  is  via the presence of classifier Cat_cat for fibrations
// injective symbol Homd_fibr [A : Cat] (M: Obj (Functor A Cat_cat)) [Y : Obj A] [Y': Obj A] (a: Hom Y Y') (f : Obj (fapp0 M Y)) (h : Obj (fapp0 M Y')) : TYPE
// ≔ @Hom (fapp0 M Y') (fapp0 (fapp1 M a) f) h;



// ===== END OF BASIC KERNEL SPECIFICATION =====


// ===== START OF EXTRA KERNEL SPECIFICATION =====

//  More rewrites/unif rules on solution/value terms 
// (required when extensionality rewrites for Set is enabled)

// naturality direct
//  ϵ._X _∘> G a  ↪  (F a) _∘> ϵ._X'
// was SLOW
rule fapp1 (hom_cov _) (@fapp1 _ _ $G $X/*/!\*/ $X' $a) (@tapp _ _ $F $G $ϵ $X)
↪ fapp1 (hom_cov _) (tapp $ϵ $X') (fapp1 $F $a);

// naturality
//  (f _∘> ϵ._X) _∘> G a  ↪  (f _∘> F a) _∘> ϵ._X'
rule fapp1 (hom_cov $W) (@fapp1 _ _ $G $X/*/!\*/ $X' $a) (fapp1 (hom_cov $W) (@tapp _ _ $F $G $ϵ $X) $g) 
↪ fapp1 (hom_cov $W) (tapp $ϵ $X') (fapp1 (hom_cov $W) (fapp1 $F $a) $g);

// functoriality direct
// SLOW unless come before general ((f _∘> H g) _∘> H a)
// H a _∘> H g  ↪  H (a _∘> g)
rule fapp1 (hom_cov _) (@fapp1 _ _ $H $Y $Z $a) (@fapp1 _ _ $H $X $Y $g)
↪ (fapp1 $H (fapp1 (hom_cov _) $a $g)) ;

// functoriality
// slow unless must come later in file
//  ((f _∘> H g) _∘> H a)  ↪  (f _∘> H (g _∘> a))
rule fapp1 (hom_cov _) (@fapp1 _ _ $H $Y $Z $a) (fapp1 (hom_cov _) (@fapp1 _ _ $H $X $Y $g) $f)
↪ fapp1 (hom_cov _) (fapp1 $H (fapp1 (hom_cov _) $a $g)) $f ;

// associativity accumulation
//  (a _∘> (f _∘> g))  ↪  ((a _∘> f) _∘> g)
rule (fapp1 (hom_cov _) (fapp1 (hom_cov $Y) $g $f) $a) 
↪ (fapp1 (hom_cov _) $g (fapp1 (hom_cov _) $f $a));

// ===== END OF EXTRA KERNEL SPECIFICATION =====


// ===== START OF BASIC STANDARD LIBRARY PRELUDE =====

// # --- Categories ---

// composition morphism

// notation:  `f ∘> g`   or   `g <∘ f`   for  `compose_morph g f`
symbol compose_morph : Π [A : Cat], Π [X: Obj A], Π [Y: Obj A], Π [Z: Obj A], Π (g: Hom Y Z), Π (f: Hom X Y),  Hom X Z;

// the special global variable "compose_morph" can be recognized as a built-in by the kernel
// so this rule could be moved to kernel (without moving "compose_morph" to kernel)
// rule:    kernel/value yoneda action  is  user-facing raw composition "compose_morph"
// notation `f _∘> a`  for  `(fapp1 (hom_cov _) a) f`
// notation `a ∘>_ f`  for  `(fapp1 (hom_con _) a) f`
// f _∘> a   ≡   f ∘> a
unif_rule (fapp1 (hom_cov $W) $a) $f ≡ compose_morph $a $f ↪ [ tt ≡ tt ];

// /!\ LAMBDAPI BUG? /!\
// NOTE: `fapp1` is not injective, 
// therefore this extra obvious congruence would be convenient to avoid manual rewrites in proofs: 
unif_rule fapp1 $H (fapp1 (hom_cov $W) $a $f) ≡ fapp1 $H (compose_morph $a $f) ↪ [ tt ≡ tt ];

// identity morphism

// notation: id
injective symbol identity_morph : Π[A : Cat], Π(X: Obj A), Hom X X;

// action on identity
// id _∘> a  ↪  a
rule ((fapp1 (hom_cov $W) $a) (identity_morph _)) ↪ $a;

// id ∘> f  ↪  f     alt notation:  f <∘ id  ↪  f    
rule compose_morph $f (identity_morph _) ↪ $f;
// f ∘> id  ↪  f     alt notation:  id <∘ f  ↪  f
rule compose_morph (identity_morph _) $f ↪ $f;

// associativity accumulation
// a ∘> (f _∘> g)  ↪  (a ∘> f) _∘> g
rule (compose_morph (fapp1 (hom_cov $Y) $g $f) $a) 
↪ (fapp1 (hom_cov _) $g (compose_morph $f $a));


// # --- Functors ---

// F id  ↪  id
rule fapp1 $F (identity_morph $X) ↪ identity_morph (fapp0 $F $X);

// functoriality direct
// F a' ∘> F a  ↪  F (a' ∘> a) 
rule compose_morph (@fapp1 _ _ $F $Y $Z $a) (@fapp1 _ _ $F $X $Y $a')
  ↪ fapp1 $F (compose_morph $a $a');

/// functoriality
// (f _∘> F a') ∘> F a  ↪  f _∘> F (a' ∘> a)
rule compose_morph (@fapp1 _ _ $F $Y $Z $a) (fapp1 (hom_cov $W) (@fapp1 _ _ $F $X $Y $a') $f)
↪ (fapp1 (hom_cov $W) (fapp1 $F (compose_morph $a $a')) $f);


// # --- Natural Transformations ---

//  (id)._X  ↪  id 
rule tapp (@identity_morph (Functor _ $B) $F) $I ↪ identity_morph (fapp0 $F $I);

// (ϵ ∘> ϵ')._X  ↪  (ϵ)._X ∘> (ϵ')._X 
rule tapp (@compose_morph (Functor _ $B) $X $Y $Z $ϵ' $ϵ) $K
   ↪ @compose_morph $B (fapp0 $X $K) (fapp0 $Y $K) (fapp0 $Z $K) (tapp $ϵ' $K) (tapp $ϵ $K);

// naturality direct
//  ϵ._X ∘> G a  ↪  (F a) _∘> ϵ._X'
rule compose_morph (@fapp1 _ _ $G $X/*/!\*/ $X' $a) (@tapp _ _ $F $G $ϵ $X)
↪ fapp1 (hom_cov _) (tapp $ϵ $X') (fapp1 $F $a);

// naturality
//  (f _∘> ϵ._X) ∘> G a  ↪  (f ∘> F a) _∘> ϵ._X'
rule compose_morph (@fapp1 _ _ $G $X/*/!\*/ $X' $a) (fapp1 (hom_cov $Y) (@tapp _ _ $F $G ( $ϵ) $X) $f)
↪ fapp1 (hom_cov $Y) (tapp ( $ϵ) $X') (compose_morph (fapp1 $F $a) $f);


// # --- Admissible associativity ---

// OPTIONAL, ADMISSIBLE, STILL IS CONFLUENT
// helps for for the unif_rule rewrite_rule interleaving problem 
// too general looks more like admissibility meta theorem, 
// could restrict to accomodate only atomic compositions, or could "make _∘> sequential" (not clear: `fapp1` or `fapp1 (hom_cov _)` sequential ?)
//  (a _∘> (f ∘> g))  ↪  ((a _∘> f) _∘> g)
rule (fapp1 (hom_cov _) (compose_morph $g $f) $a) 
↪ (fapp1 (hom_cov _) $g (fapp1 (hom_cov _) $f $a));


// # --- Set/groupoid equality of base type theory ---

constant symbol = : Π [a: Type], τ a → τ a → Type; /* ω-groupoid vs  → Prop */
notation = infix 10;

constant symbol eq_refl : Π [a: Type], Π x: τ a, τ (x = x);
symbol ind_eq : Π [a: Type], Π [x: τ a], Π [y: τ a], τ (x = y) → Π p: (τ a → Type), τ (p y) → τ (p x);
builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ ind_eq;

constant symbol Π_ : Π [a], (τ a → Type) → Type;
notation Π_ quantifier;
rule τ (@Π_ $a $b) ↪ Π x : τ $a, τ ($b x);


// # --- Equational extensionality for functor category, see below for Set category ---

symbol Eqs [A : Type] [B : τ A → Type ] (ϵ ϵ' : Π X : τ A,τ (B X)) : TYPE
  ≔ Π X : τ A, τ (ϵ X = ϵ' X);

// induction/transport structures are preserved below, no explicit map required
// NOTE: see rule for Set below. TODO: add other rewrite for (Product _ _) etc.
// apparently both rules are required
rule τ (@= (@Hom_Type (Functor $A $B) $F $G) $ϵ $ϵ') ↪ Eqs (tapp $ϵ) (tapp $ϵ');
rule τ (@= (@Transf_Type $A $B $F $G) $ϵ $ϵ') ↪ Eqs (tapp $ϵ) (tapp $ϵ');

injective symbol product_family [A : Cat] [B : Cat] [F : Obj (Functor A B)] [G : Obj (Functor A B)] 
(P : Π X : Obj A, Hom (fapp0 F X) (fapp0 G X) → Type): Hom F G → Type;

// rule must be in applied form, so product_family is not auto rewriteen
rule product_family $P $ϵ  ↪  `Π_ X , $P X (tapp $ϵ X);
 
rule (ind_eq $H (product_family $P) $x) $X  ↪  ind_eq ($H $X) ($P $X) ($x $X);

// test
assert [A : Cat] [B : Cat] [F : Obj (Functor A B)] [G : Obj (Functor A B)]
  (ϵ ϵ' : Hom F G) (H : τ (ϵ = ϵ')) 
   (P : Π X : Obj A, Hom (fapp0 F X) (fapp0 G X) → Type) 
   (p : Π X : Obj A, τ (P X (tapp ϵ' X))) (X : Obj A) ⊢ 
eq_refl _ : τ (ind_eq H (product_family P) p X 
 = ind_eq (H X) (P X) (p X));


// # --- Constructors/makers for structures ---

//   (f ∘> g) ∘> h  =  f ∘> (g ∘> h)
injective symbol categorial_TYPE Obj Hom 
 (compose_morph : Π [X: τ Obj], Π [Y: τ Obj], Π [Z: τ Obj], Π (g: τ (Hom Y Z)), Π (f: τ (Hom X Y)), τ (Hom X Z)) : TYPE
 ≔ Π [X Y Z W : τ Obj] (f : τ (Hom X Y)) (g : τ (Hom Y Z)) (h : τ (Hom Z W)),
  τ ((compose_morph _ _ _  h (compose_morph _ _ _ g f))
    = (compose_morph _ _ _ (compose_morph _ _ _ h g) f));

constant symbol mkCat_ : Π (Obj : Type) (Hom : Π (X:τ Obj) (Y: τ Obj), Type)
(compose_morph : Π [X: τ Obj], Π [Y: τ Obj], Π [Z: τ Obj], Π (g: τ (Hom Y Z)), Π (f: τ (Hom X Y)), τ (Hom X Z)), Cat;

rule @Obj (mkCat_ $O $H $C) ↪ τ $O;
rule @Hom (mkCat_ $O $H $C) $X $Y ↪ τ ($H $X $Y);
rule @compose_morph (mkCat_ $O $H $C) ↪ $C;

symbol mkCat : Π (Obj : Type) (Hom : Π (X:τ Obj) (Y: τ Obj), Type)
(compose_morph : Π [X: τ Obj], Π [Y: τ Obj], Π [Z: τ Obj], Π (g: τ (Hom Y Z)), Π (f: τ (Hom X Y)), τ (Hom X Z))
(categorial : categorial_TYPE Obj Hom compose_morph), Cat
  ≔ λ Obj Hom compose_morph _, @mkCat_ Obj Hom compose_morph;

// F a' ∘> F a  = F (a' ∘> a) 
injective symbol functoriality_TYPE  (A : Cat) (B : Cat) (fapp0 : Π(X: Obj A), Obj B)
(fapp1 : Π[X: Obj A], Π[Y: Obj A], Π(a: Hom X Y), Hom (fapp0 X) (fapp0 Y)) : TYPE ≔ 
Π [X Y Z : Obj A] (a : Hom Y Z) (a' : Hom X Y),
  τ (compose_morph (fapp1 _ _ a) (fapp1 _ _ a')
    = fapp1 _ _ (compose_morph a a'));

constant symbol mkFunctor_ [A : Cat] [B : Cat] : Π (fapp0 : Obj A → Obj B)
(fapp1 : Π[X: Obj A], Π[Y: Obj A], Π(a: Hom X Y), Hom (fapp0 X) (fapp0 Y)),  Obj (Functor A B);

rule fapp0 (mkFunctor_ $fapp0 $fapp1) ↪ $fapp0;
rule fapp1 (mkFunctor_ $fapp0 $fapp1) $a ↪ $fapp1 _ _ $a;
    
symbol mkFunctor (A : Cat) (B : Cat) : Π (fapp0 : Obj A → Obj B)
(fapp1 : Π[X: Obj A], Π[Y: Obj A], Π(a: Hom X Y), Hom (fapp0 X) (fapp0 Y))
(functoriality: functoriality_TYPE A B fapp0 fapp1),  Obj (Functor A B)
  ≔ λ fapp0 fapp1 _, @mkFunctor_ A B fapp0 fapp1;

constant symbol mkTransf_ [A : Cat] [B : Cat] [F G : Obj (Functor A B)] : 
 Π (tapp : Π (X: Obj A), Hom (fapp0 F X) (fapp0 G X)), Transf F G;

rule tapp (mkTransf_ $tapp) ↪ $tapp;

 //  ϵ._X ∘> G f  =  F f ∘> ϵ._Y
injective symbol naturality_TYPE [A : Cat] [B : Cat] (F G : Obj (Functor A B)) (tapp : Π (X: Obj A), Hom (fapp0 F X) (fapp0 G X)) : TYPE ≔ 
Π [X : Obj A] [Y : Obj A] (f : Hom X Y),
τ ((compose_morph (fapp1 G f) (tapp X))
  = (compose_morph (tapp Y) (fapp1 F f)));
 
symbol mkTransf [A : Cat] [B : Cat] (F G : Obj (Functor A B)) : 
Π (tapp : Π (X: Obj A), Hom (fapp0 F X) (fapp0 G X)),
Π (naturality : naturality_TYPE F G tapp), Transf F G ≔ λ tapp _, @mkTransf_ A B F G tapp;


// # --- Test 1, Super Yoneda Functor Benchmark 1 : by reflexivity proofs only ---

symbol compose_functors_ : Π[A:Cat], Π[B:Cat], Π[C:Cat], Π(F: Obj (Functor B C)), Π(G: Obj (Functor A B)), Obj (Functor A C)
≔ begin
  assume A B C F G;
  apply mkFunctor
  { refine (λ x, fapp0 F (fapp0 G x));
  }
  { assume X Y a; refine (fapp1 F (fapp1 G a));
  }
  { assume X Y Z a a'; refine (eq_refl _);
  }
end;

symbol super_yoneda_functor_1 : Π [A : Cat], Π [B : Cat], Π (W: Obj A), Obj (Functor (Functor B A) (Functor B Set))
≔ begin
  assume A B W;
  apply mkFunctor
  { assume F; refine (compose_functors_ (hom_cov W) F);
  }
  { assume F G ϵ; simplify;
    apply mkTransf
    { refine (λ X, (fapp1 (hom_cov W) (tapp ϵ X)))
    }
    { simplify; reflexivity;
    }
  }
  { simplify; reflexivity;
   }
end;


// # --- Equational extensionality for Set category, Cat category ---

// remember the above: rule @Hom Set $X $Y ↪ (τ $X → τ $Y);
// these express the structure-preserving of this rule; no explicit map required.

// for Set, OK to rewrite directly, rather than mere convertibility
rule (fapp1 (@hom_cov Set $W) $a) $f ↪ compose_morph $a $f;

rule (@identity_morph Set $X) $x ↪ $x;
rule (@compose_morph Set _ _ _ $f $g) $x ↪ $f ($g $x) ;

rule τ (@= (@Hom_Type Set $X $Y) $f $g) ↪ Eqs $f $g;

// for Cat, OK to rewrite directly, rather than mere convertibility
rule (fapp1 (@hom_cov Cat_cat $W) $a) $f ↪ compose_morph $a $f;

rule fapp0 (@identity_morph Cat_cat $A) $X ↪ $X;
// /!\ LAMBDAPI BUG? /!\ slow unless explicit `@fapp1 $A $A`
rule @fapp1 $A $A (@identity_morph Cat_cat $A) _ _ $a ↪ $a;

rule fapp0 (@compose_morph Cat_cat $A $B $C $G $F) $X
  ↪ (fapp0 $G (fapp0 $F $X));
rule fapp1 (@compose_morph Cat_cat $A $B $C $G $F) $a
  ↪ (fapp1 $G (fapp1 $F $a));

symbol compose_functors [A:Cat] [B:Cat] [C:Cat] (F: Obj (Functor B C)) (G: Obj (Functor A B)) : 
Obj (Functor A C) ≔ @compose_morph Cat_cat _ _ _ F G; 

// TODO ? two rules? second rule assuming $f $g have same objects-map?
//                    ... then lack grammar/elaboration for "function above another function"
// rule τ (@= (@Hom_Type Cat_cat $X $Y) $f $g) ↪  ... ;


// # --- Test 2, Super Yoneda Functor Benchmark 2 : alternative with extensionality for Set category ---

symbol super_yoneda_functor_2 : Π [A : Cat], Π [B : Cat], Π (W: Obj A), Obj (Functor (Functor B A) (Functor B Set))
≔ begin
  assume A B W;
  apply mkFunctor
  { assume F; refine (compose_functors (hom_cov W) F);
  }
  { assume F G ϵ; simplify;
    apply mkTransf
    { refine (λ X, (fapp1 (hom_cov W) (tapp ϵ X)))
    }
    { simplify; reflexivity;
    }
  }
  { simplify; reflexivity;
    // ALTERNATIVE proof when none this rewrite rule (a _∘> (f ∘> g))  ↪  ((a _∘> f) _∘> g)
    // interleaving unif_rule rewrite_rule problem 
    // simplify; assume F G H ϵ ϵ' X f;
    // rewrite left (rule_fapp1_hom_cov (tapp ϵ X) (tapp ϵ' X));
    // reflexivity;
   }
end;


// # --- TODO: dependent arrow category of a dependent category ---

constant symbol Total_cat [A : Cat] (M: Obj (Functor A Cat_cat)): Cat;
injective symbol Total_cat_proj [A : Cat] (M: Obj (Functor A Cat_cat)): Obj (Functor (Total_cat M) A);

// so (@hom_cov_cat (Total_cat M) (W_,W)) : Obj (Functor (Total_cat M) Cat)  is both fibred over (Total_cat M)
// and projects to ("is above")  (@hom_cov_cat A W_)
symbol hom_cov_cat_total_proj [A : Cat] (M: Obj (Functor A Cat_cat)) (W : Obj (Total_cat M)):
  Transf (@hom_cov_cat (Total_cat M) W) (compose_functors (@hom_cov_cat A (fapp0 (Total_cat_proj M) W)) (Total_cat_proj M));


// # --- TODO: Modules/profunctors without Set classifier vs functors to Set ---

// evidence that the map (λ f, m _∘> f) is transf 
// cannot use constructors mkTransf,
// proof is via meta case analysis, must assume this symbol
// .. hence its naturality prop gives new general conversion rules
constant symbol module_action : Π [A : Cat] (M : Obj (Functor A Set)) [X : Obj A],
τ (fapp0 M X) → Transf (hom_cov X) M;

// notation `m ⋅>_ f` for  tapp (module_action _ m) _ f
// m ⋅>_ f  ↪ M f m , 
// and in particular when M is  compose_fuctor (hom_cov W) F
// m ⋅>_ f  ↪   m _∘> F f    
rule tapp (module_action $M $m) $Y $f ↪ fapp1 $M $f $m;

// REMARK: anticipating adjunctions, module_action is motivated by adjunctions formulations
//  η ⋅>_ g                                ↪   η _∘> F g  (hom_cov) =   Φ g    ...   
//  f _⋅> ϵ (abbreviates ϵ ⋅>_ f on Aᵒᵖ)   ↪   G f ∘>_ ϵ  (hom_con) =   Γ f    ...   
// so for this transpose operation, η is in special position of data  η _∘>    (in hom_cov)
// but usually for antecedent/consequent forms it is in position of actor  η ∘>_   (in hom_con)
// similarly for data position  ∘>_ ϵ   (in hom_con)  vs  actor position  _∘> ϵ   (in hom_cov)

// TODO: double category DblCat ? so a bimodule is  A^op x A -> Set  but viewed as an relation morphism in DblCat? 
// TODO: half-double category (sigma A. A -> Set) where A can vary

// ===== END OF BASIC STANDARD LIBRARY PRELUDE =====


// # --- Test 3, Utilities ---

symbol rule_functoriality_TYPE (A : Cat) (B : Cat) (fapp0 : Π(X: Obj A), Obj B)
(fapp1' : Π[X: Obj A], Π[Y: Obj A], Π(a: Hom X Y), Hom (fapp0 X) (fapp0 Y)) : TYPE ≔ 
Π [X Y Z : Obj A] (a : Hom Y Z) (a' : Hom X Y) [W : Obj B] (f : Hom W (fapp0 X)),
  τ (compose_morph (fapp1' _ _ a) (fapp1 (hom_cov W) (fapp1' _ _ a') f)
    = (fapp1 (hom_cov W) (fapp1' _ _ (compose_morph a a'))) f) ;
  
symbol rule_functoriality [A:Cat] [B:Cat] (F : Obj (Functor A B))
   : rule_functoriality_TYPE A B (@fapp0 A B F) (@fapp1 A B F)
    ≔ λ X Y Z a a' W f, eq_refl _ ;
  
symbol functoriality_from_rule_functoriality (A : Cat) (B : Cat) (fapp0 : Π(X: Obj A), Obj B)
(fapp1 : Π[X: Obj A], Π[Y: Obj A], Π(a: Hom X Y), Hom (fapp0 X) (fapp0 Y))
: rule_functoriality_TYPE A B fapp0 fapp1 → functoriality_TYPE A B fapp0 fapp1 
≔ λ H X Y Z a a', (H X Y Z a a' _ (identity_morph _));

// id _∘> a  ↪  a
assert A [W : Obj A] [Y : Obj A] (a : Hom W Y) ⊢ ( (fapp1 (hom_cov W) a) (identity_morph _)) ≡ a;

// a _∘> id  ≡  a
assert A [W : Obj A]  ⊢ ( (fapp1 (hom_cov W) (identity_morph _))) ≡ identity_morph _;

symbol rule_fapp1_hom_cov [A : Cat] [W X Y : Obj A] (aa : Hom X Y) (f : Hom W X):
τ ((fapp1 (hom_cov W) aa) f = compose_morph aa f) ≔ eq_refl _;

symbol rule_accumulation_transf [A : Cat] [B : Cat] (F : Obj (Functor A B)) (G : Obj (Functor A B))
  (ϵ : Hom F G) (X : Obj A) [Y : Obj B] (f : Hom Y (fapp0 F X)) [Y' : Obj B] (a : Hom Y' Y) :
   τ( (compose_morph (fapp1 (hom_cov Y) (tapp ( ϵ) X) f) a) 
  = (fapp1 (hom_cov Y') (tapp ( ϵ) X)) (compose_morph f a)) ≔ eq_refl _;

injective symbol rule_naturality_TYPE [A : Cat] [B : Cat] (F G : Obj (Functor A B)) (tapp : Π (X: Obj A), Hom (fapp0 F X) (fapp0 G X)) : TYPE ≔ 
Π [X : Obj A] [X' : Obj A] (a : Hom X X') [Y : Obj B] (f : Hom Y (fapp0 F X)),
τ( (compose_morph (fapp1 G a) (fapp1 (hom_cov Y) (tapp X) f))
  =  (fapp1 (hom_cov Y) (tapp X') (compose_morph (fapp1 F a) f)));

symbol rule_naturality [A : Cat] [B : Cat] [F : Obj (Functor A B)] [G : Obj (Functor A B)]
(ϵ : Transf F G)
: rule_naturality_TYPE F G (tapp ( ϵ)) ≔ λ X X' a Y f , eq_refl _;

// user-facing naturality from computational rule naturality
symbol naturality_from_rule_naturality [A : Cat] [B : Cat] [F G : Obj (Functor A B)] [tapp : Π (X: Obj A), Hom (fapp0 F X) (fapp0 G X)] 
: rule_naturality_TYPE F G tapp → naturality_TYPE F G tapp
≔ λ H X X' a, (H X X' a _ (identity_morph (fapp0 F X)));

injective symbol rule_naturality_direct_TYPE [A : Cat] [B : Cat] (F G : Obj (Functor A B)) (tapp : Π (X: Obj A), Hom (fapp0 F X) (fapp0 G X)) : TYPE ≔ 
Π [X : Obj A] [X' : Obj A] (a : Hom X X'),
τ( compose_morph (fapp1 G a) (tapp X)
  = fapp1 (hom_cov _) (tapp X') (fapp1 F a));

symbol rule_naturality_direct [A : Cat] [B : Cat] [F : Obj (Functor A B)] [G : Obj (Functor A B)]
(ϵ : Transf F G) 
: rule_naturality_direct_TYPE F G (tapp ( ϵ)) ≔ λ X X' a , eq_refl _;
