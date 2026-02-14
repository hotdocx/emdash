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

constant symbol Functor : Π(A : Cat), Π(B : Cat), TYPE;

constant symbol Functor_Type : Π(A : Cat), Π(B : Cat), Type;
rule τ (@Functor_Type $A $B) ↪ @Functor $A $B;

symbol fapp0 : Π[A : Cat], Π[B : Cat], Π(F : Functor A B), Obj A → Obj B;
symbol fapp1 : Π[A : Cat], Π[B : Cat], Π(F : Functor A B),
  Π[X: Obj A], Π[Y: Obj A], Π(a: Hom X Y), Hom (fapp0 F X) (fapp0 F Y);

// ok these rules concerned `Functor A B`, but what is `@Hom (Functor_cat _ _)` ? answer:


// # --- Natural Transformations ---

constant symbol Transf : Π [A : Cat], Π [B : Cat], Π (F : Functor A B), Π (G : Functor A B), TYPE;

constant symbol Transf_Type : Π [A : Cat], Π [B : Cat], Π (F : Functor A B), Π (G : Functor A B), Type;
rule τ (@Transf_Type $A $B $F $G) ↪ @Transf $A $B $F $G;

// notation:  (ϵ)._X  for  tapp ϵ X
symbol tapp : Π [A : Cat], Π [B : Cat], Π [F : Functor A B], Π [G : Functor A B],
  Π (ϵ : Transf F G), Π (X: Obj A), Hom (fapp0 F X) (fapp0 G X);


// # --- Functor category ---

constant symbol Functor_cat : Π(A : Cat), Π(B : Cat), Cat;

unif_rule Obj $Z ≡ (Functor $A $B) ↪ [ $Z ≡ (Functor_cat $A $B) ];

// structure-preserving (components) expressed indirectly below, no explicit map required for this rule
rule @Hom (Functor_cat _ _) $F $G ↪ Transf $F $G;
  

// # --- Set category classifier, discrete fibrations, yoneda representable Functor ---

// category Set of types/sets/groupoids, classifier for discrete modules/fibrations which become Functor (A, Set)
// TODO: category Cat_cat of categories, classifier for non-discrete fibrations which become Functor (A, Cat_cat)
constant symbol Set : Cat;

unif_rule Obj $A ≡ Type ↪ [ $A ≡ Set ];

// see below section "extensionality for Set" for structure-preservation
rule @Hom Set $X $Y ↪ (τ $X → τ $Y);

// yoneda covarient embedding functor to Set; also TODO: contravariant Yoneda
// this is a "fully-saturated" constructor `@hom_cov A W : Functor A Set` inside kernel,
// unlike `compose_morph` which has a Π type
constant symbol hom_cov : Π [A : Cat], Π (W: Obj A), Functor A Set;
// constant symbol hom_con : Π [A : Cat], Π (W: Obj A), Obj (Functor Aᵒᵖ Set);

rule fapp0 (hom_cov $X) $Y ↪ Hom_Type $X $Y;

// # --- Cat category classifier, fibrations, isofibrations, yoneda representable Functor ---

constant symbol Cat_cat : Cat;

unif_rule Obj $A ≡ Cat ↪ [ $A ≡ Cat_cat ];

rule @Hom Cat_cat $X $Y ↪ Functor $X $Y;

constant symbol hom_cov_cat : Π [A : Cat], Π (W: Obj A), Functor A Cat_cat;

// the objects-map of hom_cov_cat is hom_cov
rule Obj (fapp0 (hom_cov_cat $W) $Y) ↪ Hom $W $Y;
rule fapp0 (fapp1 (hom_cov_cat $W) $a) $f ↪ (fapp1 (hom_cov $W) $a) $f;


// ===== END OF BASIC KERNEL SPECIFICATION =====


// ===== START OF EXTRA KERNEL SPECIFICATION =====

//  More rewrites/unif rules on solution/value terms 
// (required when extensionality rewrites for Set is enabled)

// naturality direct
//  ϵ._X _∘> G a  ↪  (F a) _∘> ϵ._X'
rule fapp1 (hom_cov _) (@fapp1 _ _ $G $X $X' $a) (@tapp _ _ $F $G $ϵ $X)
↪ fapp1 (hom_cov _) (tapp $ϵ $X') (fapp1 $F $a);

// naturality
//  (f _∘> ϵ._X) _∘> G a  ↪  (f _∘> F a) _∘> ϵ._X'
rule fapp1 (hom_cov $W) (@fapp1 _ _ $G $X $X' $a) (fapp1 (hom_cov $W) (@tapp _ _ $F $G $ϵ $X) $g) 
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
rule tapp (@identity_morph (Functor_cat _ $B) $F) $I ↪ identity_morph (fapp0 $F $I);

// (ϵ ∘> ϵ')._X  ↪  (ϵ)._X ∘> (ϵ')._X 
rule tapp (@compose_morph (Functor_cat _ $B) $X $Y $Z $ϵ' $ϵ) $K
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
rule ind_eq (eq_refl $x) $p $u ↪ $u;
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
rule τ (@= (@Hom_Type (Functor_cat $A $B) $F $G) $ϵ $ϵ') ↪ Eqs (tapp $ϵ) (tapp $ϵ');
rule τ (@= (@Transf_Type $A $B $F $G) $ϵ $ϵ') ↪ Eqs (tapp $ϵ) (tapp $ϵ');

injective symbol product_family [A : Cat] [B : Cat] [F : Functor A B] [G : Functor A B] 
(P : Π X : Obj A, Hom (fapp0 F X) (fapp0 G X) → Type): Hom F G → Type;

// rule must be in applied form, so product_family is not auto rewriteen
rule product_family $P $ϵ  ↪  `Π_ X , $P X (tapp $ϵ X);
 
rule (ind_eq $H (product_family $P) $x) $X  ↪  ind_eq ($H $X) ($P $X) ($x $X);

// test
assert [A : Cat] [B : Cat] [F : Functor A B] [G : Functor A B]
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
(fapp1 : Π[X: Obj A], Π[Y: Obj A], Π(a: Hom X Y), Hom (fapp0 X) (fapp0 Y)),  Functor A B;

rule fapp0 (mkFunctor_ $fapp0 $fapp1) ↪ $fapp0;
rule fapp1 (mkFunctor_ $fapp0 $fapp1) $a ↪ $fapp1 _ _ $a;
    
symbol mkFunctor (A : Cat) (B : Cat) : Π (fapp0 : Obj A → Obj B)
(fapp1 : Π[X: Obj A], Π[Y: Obj A], Π(a: Hom X Y), Hom (fapp0 X) (fapp0 Y))
(functoriality: functoriality_TYPE A B fapp0 fapp1),  Functor A B
  ≔ λ fapp0 fapp1 _, @mkFunctor_ A B fapp0 fapp1;

constant symbol mkTransf_ [A : Cat] [B : Cat] [F G : Functor A B] : 
 Π (tapp : Π (X: Obj A), Hom (fapp0 F X) (fapp0 G X)), Transf F G;

rule tapp (mkTransf_ $tapp) ↪ $tapp;

 //  ϵ._X ∘> G f  =  F f ∘> ϵ._Y
injective symbol naturality_TYPE [A : Cat] [B : Cat] (F G : Functor A B) (tapp : Π (X: Obj A), Hom (fapp0 F X) (fapp0 G X)) : TYPE ≔ 
Π [X : Obj A] [Y : Obj A] (f : Hom X Y),
τ ((compose_morph (fapp1 G f) (tapp X))
  = (compose_morph (tapp Y) (fapp1 F f)));
 
symbol mkTransf [A : Cat] [B : Cat] (F G : Functor A B) : 
Π (tapp : Π (X: Obj A), Hom (fapp0 F X) (fapp0 G X)),
Π (naturality : naturality_TYPE F G tapp), Transf F G ≔ λ tapp _, @mkTransf_ A B F G tapp;


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

symbol compose_functors [A:Cat] [B:Cat] [C:Cat] (F: Functor B C) (G: Functor A B) : 
Functor A C ≔ @compose_morph Cat_cat _ _ _ F G; 

// TODO ? two rules? second rule assuming $f $g have same objects-map?
//                    ... then lack grammar/elaboration for "function above another function"
// rule τ (@= (@Hom_Type Cat_cat $X $Y) $f $g) ↪  ... ;


// # --- Test 2, Super Yoneda Functor Benchmark 2 : alternative with extensionality for Set category ---

symbol super_yoneda_functor_2 : Π [A : Cat], Π [B : Cat], Π (W: Obj A), Functor (Functor_cat B A) (Functor_cat B Set)
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


// # --- TODO: ω-category, arrow/comma category, dependent arrow category of a dependent/fibration category ---

inductive τΣ_ [a : Type] (P : τ a → Type) : TYPE ≔
| Struct_sigma [a P] : Π (sigma_Fst : τ a) (sigma_Snd : τ (P sigma_Fst) ), @τΣ_ a P;
notation τΣ_ quantifier;

constant symbol Σ_ [a : Type] (P : τ a → Type) : Type; notation Σ_ quantifier;
rule τ (Σ_ $P) ↪ τΣ_ $P;

injective symbol sigma_Fst [a P] (s : @τΣ_ a P) : τ a;
rule sigma_Fst (Struct_sigma $1 $2) ↪ $1;

injective symbol sigma_Snd [a P] (s : @τΣ_ a P) : τ (P (sigma_Fst s));
rule sigma_Snd (Struct_sigma $1 $2) ↪ $2;

constant symbol Total_cat [A : Cat] (M: Functor A Cat_cat): Cat;
injective symbol Total_cat_proj [A : Cat] (M: Functor A Cat_cat): Functor (Total_cat M) A;

rule Obj (Total_cat $M) ↪ `τΣ_ X : Obj _, Obj_Type (fapp0 $M X);

rule @Hom (Total_cat $M) $Y_f $Y'_f' 
↪ `τΣ_ a : Hom (sigma_Fst $Y_f) (sigma_Fst $Y'_f'), 
      @Hom_Type (fapp0 $M (sigma_Fst $Y'_f')) (fapp0 (fapp1 $M a) (sigma_Snd $Y_f)) (sigma_Snd $Y'_f');

rule fapp0 (Total_cat_proj $M) $Y_f ↪ sigma_Fst $Y_f;
rule fapp1 (Total_cat_proj $M) $a_ϕ ↪ sigma_Fst $a_ϕ;



// # --- TODO: Modules/profunctors without Set classifier vs functors to Set ---

// evidence that the map (λ f, m _∘> f) is transf 
// cannot use constructors mkTransf,
// proof is via meta case analysis, must assume this symbol
// .. hence its naturality prop gives new general conversion rules
constant symbol module_action : Π [A : Cat] (M : Functor A Set) [X : Obj A],
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

// ===== END OF BASIC STANDARD LIBRARY PRELUDE =====

