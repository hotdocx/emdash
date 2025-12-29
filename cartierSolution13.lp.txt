/* https://github.com/1337777/cartier/blob/master/cartierSolution13.lp 
https://github.com/1337777/cartier/blob/master/Kosta_Dosen_outline_alt.pdf

Kosta Dosen's functorial programming: « m— » (read as « emdash » or « modos »), a new proof assistant for schemes.
  A computational logic (co-inductive) interface for algebraic geometry schemes.

  (A short description at the end of this file.)

cartierSolution13.lp : DOSEN'S FUNCTORIAL PROGRAMMING
cartierSolution14.lp : 1+2=3 VIA 3 METHODS: HIGHER DATA TYPE, ADJUNCTION, COLIMIT
cartierSolution15.lp : POLYNOMIAL FUNCTORS AND CATEGORIES AS POLYNOMIAL COMONOIDS
cartierSolution16.lp : COMPUTATIONAL LOGIC (CO-INDUCTIVE) INTERFACE FOR SHEAVES AND SCHEMES

https://github.com/1337777/cartier/blob/master/cartierSolution13.lp 
https://github.com/1337777/cartier/blob/master/cartierSolution14.lp 
https://github.com/1337777/cartier/blob/master/cartierSolution15.lp 
https://github.com/1337777/cartier/blob/master/cartierSolution16.lp 
https://github.com/1337777/cartier/blob/master/Kosta_Dosen_outline_alt.pdf 
https://github.com/1337777/cartier/blob/master/Kosta_Dosen_outline_alt.docx 

OUTLINE OF cartierSolution13.lp :

# INTRODUCTION TO LAMBDAPI, PRELIMINARIES

# PRELIMINARIES REMINDERS ABOUT DEPENDENT TYPES
  AND IMPLEMENTING CONTEXT-EXTENSION 
  (CATEGORIES WITH FAMILIES) WHICH COMPUTES# SIGMA-SUM: PART 1

# CATEGORIES, FUNCTORS, ISOFIBRATIONS OF CATEGORIES

# CONTEXT EXTENSION FOR CATEGORIES

# SIGMA-SUM FOR (ISO)FIBRATIONS OF CATEGORIES

# PI-PRODUCT FOR (ISO)FIBRATIONS OF CATEGORIES

# MODULES (PROFUNCTORS), UNIT HOM MODULES, AND TRANSFORMATIONS,
* YONEDA ACTION

# CUT-ELIMINATION AND ASSOCIATIVITY METATHEOREM

# PRODUCT CATEGORY

# PRODUCT CATEGORY AS A TRIVIAL ISOFIBRATION

# INDUCTIVE DATA TYPE, EXAMPLE OF THE JOIN CATEGORY

# DEPENDENT (ISO)FIBRATIONS OF MODULES

# CONTEXT EXTENSION FOR MODULES (PROFUNCTORS)

# SIGMA-SUM AND PI-PRODUCT OF FIBRED PROFUNCTORS

# FIBRATIONS: CARTESIAN TRANSPORT

# FIBRATIONS: COMMA CATEGORY

# FIBRATIONS: EXAMPLE OF FIBRED PRODUNCTOR, SQUARES FIBRED BY THEIR DIAGONAL

# CATEGORY OF ELEMENTS AS AN INSTANCE OF THE COMMA FIBRATION CATEGORY

# TENSOR (AND KAN EXTENSIONS AND CO-YONEDA REDUCTIONS) HOM FOR MODULES (PROFUNCTORS)

# INTERNAL HOM (IMPLICATION), LAMBDA CALCULUS FOR MODULES (PROFUNCTORS)

# SETS, UNDERLYING GROUPOIDS, DISCRETE/GROUPOIDS AS CATEGORIES, UNIVALENT CATEGORIES

# CONTAINER SETS, POLYNOMIAL MODULES, POLYNOMAIL FUNCTORS - PART 1. (cartierSolution15.lp FOR PART 2)

# ADJUNCTION OF FUNCTORS BETWEEN CATEGORIES

# WEIGHTED LIMITS, RIGHT ADJOINTS PRESERVE WEIGHTED LIMITS

# DUALITY, COVARIANT VS CONTRAVARIANCE, LEFT ADJOINT PRESERVE WEIGHTED COLIMITS BY DUALITY

*/

/*
> lambdapi --version  
2.5.0 # https://github.com/Deducteam/lambdapi https://github.com/Deducteam/lambdapi-stdlib
> cat lambdapi.pkg
package_name = modos
root_path    = modos
*/

// require open Blanqui.Lib.Type Blanqui.Lib.Type Blanqui.Lib.Eq;
verbose 10;
flag "print_contexts" on; flag "print_domains" on; flag "print_meta_types" on;
// flag "print_implicits" on;
// debug +a; //debug +acdeghiklmoprsyuvxyz;
print coerce_rule; // /!\ only for console mode: print unif_rule;
// search "spine = (cartierSolution13.cat → cartierSolution13.cat) , hyp = cartierSolution13.cat";


/*****************************************
* # INTRODUCTION TO LAMBDAPI, PRELIMINARIES
******************************************/

// infinity groupoid, as in homotopy type theory
constant symbol Type : TYPE;
injective symbol τ : Type → TYPE;
builtin "T" ≔ τ;
builtin "Prop" ≔ Type;
builtin "P" ≔ τ;

constant symbol = [a] : τ a → τ a → Type /* not Prop */;
notation = infix 10;

constant symbol eq_refl [a] (x:τ a) : τ (x = x);
constant symbol ind_eq [a] [x y:τ a] : τ (x = y) → Π p, τ (p y) → τ (p x);

builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ ind_eq;

opaque symbol eq_transf [a] [x y z:τ a] : τ (x = y) → τ (y = z) → τ (x = z)
≔ begin
assume a x y z Hxy Hyz;  
rewrite Hxy; apply Hyz;
end;
 
constant symbol × : Type → Type → Type; notation × infix right 10;

symbol & [a b] : τ a → τ b → τ (a × b); notation & infix right 30;

symbol ₁ [a b] : τ(a × b) → τ a; notation ₁ postfix 10;
rule ($x & _)₁ ↪ $x;

symbol ₂ [a b] : τ(a × b) → τ b; notation ₂ postfix 10;
rule (_ & $x)₂ ↪ $x;

constant symbol ⊤ : Type;
constant symbol top : τ ⊤;

constant symbol ⊥ : Type;
constant symbol ⊥ₑ [p] : τ ⊥ → τ p;

constant symbol Π_ : Π [a], (τ a → Type) → Type; notation Π_ quantifier;
rule τ (@Π_ $a $b) ↪ Π x : τ $a, τ ($b x);

constant symbol →_ : Type → Type → Type; notation →_ infix right 10;
rule τ ($x →_ $y) ↪ τ $x → τ $y;

inductive τΣ_ [a : Type] (P : τ a → Type) : TYPE ≔
| Struct_sigma [a P] : Π (sigma_Fst : τ a) (sigma_Snd : τ (P sigma_Fst) ), @τΣ_ a P;
notation τΣ_ quantifier;

constant symbol Σ_ [a : Type] (P : τ a → Type) : Type; notation Σ_ quantifier;
rule τ (Σ_ $P) ↪ τΣ_ $P;

injective symbol sigma_Fst [a P] (s : @τΣ_ a P) : τ a;
rule sigma_Fst (Struct_sigma $1 $2) ↪ $1;

injective symbol sigma_Snd [a P] (s : @τΣ_ a P) : τ (P (sigma_Fst s));
rule sigma_Snd (Struct_sigma $1 $2) ↪ $2;

inductive unit : TYPE ≔ | tt : unit;

constant symbol unit_type : Type;
rule τ unit_type ↪ unit;

inductive bool : TYPE ≔
| true : bool
| false : bool;

constant symbol bool_type : Type;
rule τ bool_type ↪ bool;

symbol istrue : bool → Type;
rule istrue true ↪ ⊤
with istrue false ↪ ⊥;

symbol or : bool → bool → bool; notation or infix left 20;
rule true  or _    ↪ true
with _     or true ↪ true
with false or $b   ↪ $b
with $b    or false ↪ $b;

symbol and : bool → bool → bool; notation and infix left 7;
rule true  and $b   ↪ $b
with $b    and true ↪ $b
with false and _    ↪ false
with _     and false ↪ false;

symbol if : bool → Π [a], τ a → τ a → τ a;
rule if true  $x _ ↪ $x
with if false _ $y ↪ $y;

inductive nat : TYPE ≔
| 0 : nat
| +1 : nat → nat; notation +1 postfix 100;
builtin "0"  ≔ 0;
builtin "+1" ≔ +1;

constant symbol nat_type : Type;
rule τ nat_type ↪ nat;

symbol eqn : nat → nat → bool;
rule eqn 0 0 ↪ true
with eqn ($x +1) ($y +1) ↪ eqn $x $y
with eqn 0 (_ +1) ↪ false
with eqn (_ +1) 0 ↪ false;

(a:Type) inductive list:TYPE ≔
| □ : list a // \Box
| ⸬ : τ a → list a → list a; // ::
notation ⸬ infix right 20;

constant symbol list_type : Type → Type;
rule τ (list_type $a) ↪ list $a;

symbol ⋅ [a] : list a → list a → list a; notation ⋅ infix right 30; // \cdot
rule □ ⋅ $m ↪ $m
with ($x ⸬ $l) ⋅ $m ↪ $x ⸬ ($l ⋅ $m);

symbol filter [a] : (τ a → bool) → list a → list a;
rule filter _ □ ↪ □
with filter $p ($x ⸬ $l) ↪ if ($p $x) ($x ⸬ (filter $p $l)) (filter $p $l);

symbol ∈ [a] : (τ a → τ a → bool) → τ a → list a → bool;
rule ∈ _ _ □ ↪ false
with ∈ $beq $x ($y ⸬ $l) ↪ $beq $x $y or ∈ $beq $x $l;

symbol map [a b] : (τ a → τ b) → list a → list b;
rule map _ □ ↪ □
with map $f ($x ⸬ $l) ↪ $f $x ⸬ map $f $l;

constant symbol DEBUG_ADMIT [a : Type] : τ a;
injective symbol DEBUG_TAG1 [a : Type] : τ a → τ a; rule DEBUG_TAG1 $x ↪ $x;
injective symbol DEBUG_TAG2 [a : Type] : τ a → τ a; rule DEBUG_TAG2 $x ↪ $x;

/*****************************************
* # PRELIMINARIES REMINDERS ABOUT DEPENDENT TYPES
* AND IMPLEMENTING CONTEXT-EXTENSION 
* (CATEGORIES WITH FAMILIES) WHICH COMPUTES
******************************************/

constant symbol 
  Con : TYPE;

constant symbol
  Ty : Con → TYPE;

constant symbol
  ◇ : Con;

injective symbol
  ▹ : Π (Γ : Con), Ty Γ → Con;

notation ▹ infix right 90;

constant symbol
  Sub : Con → Con → TYPE;

symbol
  ∘ : Π [Δ Γ Θ], Sub Δ Γ → Sub Θ Δ → Sub Θ Γ;

notation ∘ infix right 80;

rule /* assoc */ 
  $γ ∘ ($δ ∘ $θ) ↪ ($γ ∘ $δ) ∘ $θ;

constant symbol
  id : Π [Γ], Sub Γ Γ;

rule /* idr */ 
  $γ ∘ id ↪ $γ
with /* idl */ 
  id ∘ $γ ↪ $γ;

symbol
  'ᵀ_ : Π [Γ Δ], Ty Γ → Sub Δ Γ → Ty Δ;

notation 'ᵀ_ infix left 70;

rule /* 'ᵀ_-∘ */ 
  $A 'ᵀ_ $γ 'ᵀ_ $δ ↪ $A 'ᵀ_( $γ ∘ $δ )
with /* 'ᵀ_-id */
  $A 'ᵀ_ id ↪ $A;

constant symbol
  Tm : Π (Γ : Con), Ty Γ → TYPE;

symbol
  'ᵗ_ : Π [Γ A Δ], Tm Γ A → Π (γ : Sub Δ Γ), Tm Δ (A 'ᵀ_ γ);

notation 'ᵗ_ infix left 70;

rule /*  'ᵗ_-∘ */ 
  $a 'ᵗ_ $γ 'ᵗ_ $δ ↪ $a 'ᵗ_( $γ ∘ $δ )
with /* 'ᵗ_-id */ 
  $a 'ᵗ_ id ↪ $a;

injective symbol
  ε : Π [Δ], Sub Δ ◇;

rule /* ε-∘ */
  ε ∘ $γ ↪ ε
with /* ◇-η */
  @ε ◇ ↪ id;

injective symbol 
  pₓ : Π [Γ A], Sub (Γ ▹ A) Γ;

injective symbol 
  qₓ : Π [Γ A], Tm (Γ ▹ A) (A 'ᵀ_ pₓ);

injective symbol 
  &ₓ : Π [Γ Δ A], Π (γ : Sub Δ Γ), Tm Δ (A 'ᵀ_ γ) → Sub Δ (Γ ▹ A);

notation &ₓ infix left 70;

rule /*  &ₓ-∘ */
  ($γ &ₓ $a) ∘ $δ ↪ ($γ ∘ $δ &ₓ ($a 'ᵗ_ $δ));

rule /*  ▹-β₁ */ 
  pₓ ∘ ($γ &ₓ $a) ↪ $γ;

rule /* ▹-β₂ */ 
  qₓ 'ᵗ_ ($γ &ₓ $a) ↪ $a;

rule /* ▹-η */
  (@&ₓ _ _ $A (@pₓ _ $A) qₓ) ↪ id;


/*****************************************
* # CATEGORIES, FUNCTORS, ISOFIBRATIONS OF CATEGORIES
******************************************/

constant symbol cat : TYPE;

constant symbol func : Π (A B : cat), TYPE;
constant symbol func_type : Π (A B : cat), Type;
rule τ (@func_type $A $B) ↪ @func $A $B;

constant symbol catd: Π (X : cat), TYPE;

constant symbol funcd : Π [X Y : cat] (A : catd X) (F : func X Y) (B : catd Y), TYPE;
constant symbol funcd_type : Π [X Y : cat] (A : catd X) (F : func X Y) (B : catd Y), Type;
rule τ (@funcd_type $X $Y $A $F $B) ↪ (@funcd $X $Y $A $F $B);

/* -----
* ## categories and functors (objects) */

constant symbol Terminal_cat : cat;

constant symbol Id_func : Π [A : cat], func A A;

symbol ∘> : Π [A B C: cat], func A B → func B C → func A C;
notation ∘> infix left 90; // compo_func

rule $X ∘> ($G ∘> $H) ↪ ($X ∘> $G) ∘> $H
with $F ∘> Id_func ↪ $F
with Id_func ∘> $F ↪ $F;

injective symbol Terminal_func :  Π (A : cat), func A Terminal_cat;

rule (@∘> $A $B $C $F (Terminal_func $B)) ↪ (Terminal_func $A)
with (Terminal_func (Terminal_cat)) ↪ Id_func;

/* -----
* ## fibred (dependent) categories */

constant symbol Terminal_catd : Π (A : cat), catd A;

symbol Fibre_catd : Π [X I : cat] (A : catd X) (x : func I X), catd I;

rule Fibre_catd $A Id_func ↪ $A
with Fibre_catd $A ($x ∘> $y) ↪ Fibre_catd (Fibre_catd $A $y) $x;
rule Fibre_catd (Terminal_catd _) _ ↪ (Terminal_catd _);

/* -----
* ## fibred (dependent) functors */

constant symbol Id_funcd : Π [X : cat] [A : catd X], funcd A Id_func A;

symbol ∘>d: Π [X Y Z : cat] [A : catd X] [B : catd Y] [C : catd Z] [F : func X Y]
[G : func Y Z], funcd A F B → funcd B G C → funcd A (F ∘> G) C;
notation ∘>d infix left 90; // compo_funcd

rule $X ∘>d ($G ∘>d $H) ↪ ($X ∘>d $G) ∘>d $H
with $F ∘>d Id_funcd ↪ $F
with Id_funcd ∘>d $F ↪ $F;

injective symbol Terminal_funcd :  Π [X Y: cat] (A : catd X) (xy : func X Y), funcd A xy (Terminal_catd Y);

injective symbol Fibre_intro_funcd : Π [X I I' : cat] (A : catd X) (x : func I X) [J : catd I'] (i : func I' I) ,
 funcd J (i ∘> x) A → funcd J i (Fibre_catd A x);

injective symbol Fibre_elim_funcd : Π [X I : cat] (A : catd X) (x : func I X), funcd (Fibre_catd A x) x A;

// naturality
rule $HH ∘>d (Fibre_intro_funcd $A $x _ $FF) ↪ (Fibre_intro_funcd $A $x _ ($HH ∘>d $FF))
with (Fibre_elim_funcd /*DON'T SPECIFY, ALLOW CONVERSION: (Fibre_catd $A $y) */ _ $x) ∘>d Fibre_elim_funcd $A $y ↪ Fibre_elim_funcd $A ($x ∘> $y);

// beta, eta
rule (Fibre_intro_funcd $A $x _ $FF) ∘>d (Fibre_elim_funcd $A $x) ↪ $FF
with (Fibre_intro_funcd $A $x Id_func (Fibre_elim_funcd $A $x)) ↪ Id_funcd;

rule Fibre_elim_funcd $A Id_func ↪ Id_funcd
with Fibre_intro_funcd $A Id_func $i $FF ↪ $FF
with (Fibre_intro_funcd /* (Fibre_catd $A $y) */ _ $x $i (Fibre_intro_funcd $A $y /* ($i ∘> $x) */ _ $FF)) 
↪ (Fibre_intro_funcd $A ($x ∘> $y) $i $FF);

rule (Terminal_funcd (Terminal_catd _) $xy) ↪ Fibre_elim_funcd (Terminal_catd _) $xy;
rule ($FF ∘>d (Terminal_funcd $B $xy)) ↪ (Terminal_funcd _ _);
rule (Terminal_funcd (Terminal_catd _) Id_func) ↪ Id_funcd; // confluent...


/*****************************************
* # CONTEXT EXTENSION FOR CATEGORIES
******************************************/

injective symbol Context_cat : Π [X : cat], catd X → cat;

injective symbol Context_elimCat_func : Π [X : cat] (A : catd X), func (Context_cat A) X;

injective symbol Context_elimCatd_funcd : Π [X : cat] (A : catd X), funcd (Terminal_catd _) (Context_elimCat_func A) A;

injective symbol Context_intro_func : Π [X Y : cat] [A : catd X] [B : catd Y] [xy : func X Y],
funcd A xy B → func (Context_cat A) (Context_cat B);

rule Context_cat (Terminal_catd $A) ↪ $A;
rule Context_elimCat_func (Terminal_catd $A) ↪ Id_func;
rule Context_elimCatd_funcd (Terminal_catd $A) ↪ Id_funcd;
rule Context_intro_func (Id_funcd) ↪ Id_func
with Context_intro_func (Terminal_funcd $A $xy) ↪ Context_elimCat_func $A ∘> $xy;

// definable symbols
injective symbol Context_intro_single_func [Y : cat] [B : catd Y] [X] (xy : func X Y)
(FF : funcd (Terminal_catd X) xy B) : func X (Context_cat B);
rule Context_intro_single_func _ $FF ↪ @Context_intro_func _ _ (Terminal_catd _) _ _ $FF;

injective symbol Context_intro_congr_func [Y : cat] [B : catd Y] [X] (xy : func X Y) 
: func (Context_cat (Fibre_catd B xy)) (Context_cat B);
rule Context_intro_congr_func $xy ↪ Context_intro_func (Fibre_elim_funcd _ $xy);

// beta rules
rule (@Context_intro_func _ _ $A $B $F $FF) ∘> (Context_elimCat_func $B) 
↪ (Context_elimCat_func $A) ∘> $F;
rule (Fibre_elim_funcd (Terminal_catd $X) (@Context_intro_func _ _ (Terminal_catd $X) $B $xy $FF)) ∘>d (Context_elimCatd_funcd $B) 
↪ $FF;

// LAMBDAPI BUG? this unification rule doesnt work... so finding an alternative
// unif_rule Context_cat $B ≡ (Context_cat (Terminal_catd (Context_cat $X))) ↪ [ $B ≡ $X];
symbol rule_Context_cat_Terminal_catd_func [X: cat] (A: catd X) 
: func (Context_cat (Terminal_catd (Context_cat A))) (Context_cat A)
≔ begin assume X A; simplify; refine Id_func; end;

// eta rules
rule Context_intro_func (Context_elimCatd_funcd $A) 
 ↪ rule_Context_cat_Terminal_catd_func $A;
rule @Context_intro_func _ _ _ _ $xy (Fibre_elim_funcd (Terminal_catd _) _) ↪ $xy;

// naturality rules
// confluent ... and both rules required despite in meta the latter conversion is derivable from the former rules
rule (@Context_intro_func $X $Y $A $B $F $FF) ∘> (@Context_intro_func $Y $Z $B $C $G $GG)
 ↪ Context_intro_func ($FF ∘>d $GG)
with $z ∘> @Context_intro_func _ _ (Terminal_catd _) _ _ $FF
↪ Context_intro_func ( (Fibre_elim_funcd (Terminal_catd _) $z)  ∘>d $FF );

assert [X Y : cat] [B : catd Y] [xy : func X Y] (FF : funcd (Terminal_catd X) xy B) [Z] [z : func Z X] ⊢  
(@Context_intro_func _ _ _ _ z (Terminal_funcd (Terminal_catd Z) z)) ∘> Context_intro_func FF
 ≡ Context_intro_func ( (Terminal_funcd (Terminal_catd Z) z)  ∘>d FF );


/*****************************************
* # SIGMA-SUM FOR (ISO)FIBRATIONS OF CATEGORIES
******************************************/

injective symbol Sigma_catd : Π [X : cat] (F : catd X) (Z : catd (Context_cat F)), catd X;

// ... beck-chevalley
rule Fibre_catd (Sigma_catd $F $Z) $G 
↪ Sigma_catd (Fibre_catd $F $G) (Fibre_catd $Z (Context_intro_func (Fibre_elim_funcd $F $G))) ;

injective symbol Sigma_intro_funcd : Π [X : cat] (F : catd X) (Z : catd (Context_cat F)), 
    funcd Z (Context_elimCat_func F) (Sigma_catd F Z);

injective symbol Sigma_elim_funcd : Π [X : cat] (F : catd X) [Z : catd (Context_cat F)] [X'] (G : func X X') [C : catd X'], 
    funcd Z ((Context_elimCat_func F) ∘> G) C → funcd (Sigma_catd F Z) G C;

// naturality
rule (Sigma_elim_funcd $F $G $CC) ∘>d $DD ↪ (Sigma_elim_funcd $F _ ($CC ∘>d $DD));
// beta
rule (Sigma_intro_funcd $F $Z) ∘>d (Sigma_elim_funcd $F $G $CC) ↪ $CC;

/* -----
* ## TODO: SIGMA-SUM WHEN CARTESIAN FIBRATION (ALONG CARTESIAN FIBRATION) */

// constructions for derived isFibration_con isFibration_cov ...


/*****************************************
* # PI-PRODUCT FOR (ISO)FIBRATIONS OF CATEGORIES
******************************************/

injective symbol Pi_catd : Π [X : cat] (F : catd X) (Z : catd (Context_cat F)), catd X;

// ... beck-chevalley
rule Fibre_catd (Pi_catd $F $Z) $G 
↪ Pi_catd (Fibre_catd $F $G) (Fibre_catd $Z (Context_intro_func (Fibre_elim_funcd $F $G))) ;

injective symbol Pi_elim_funcd : Π [X : cat] [F : catd X] [Z : catd (Context_cat F)] [X'] [x : func X' X] [E : catd X'],
funcd E x (Pi_catd F Z) →
funcd (Fibre_catd E (Context_elimCat_func (Fibre_catd F x))) (Context_intro_func (Fibre_elim_funcd F x)) Z;

// over  general  G required for naturality
injective symbol Pi_intro_funcd : Π [X' : cat] (C : catd X') [X : cat] (G : func X' X) (F : catd X) [Z : catd (Context_cat F)] 
(CC : funcd (Fibre_catd C (Context_elimCat_func (Fibre_catd F G))) (Context_intro_func (Fibre_elim_funcd F G)) Z), 
funcd C G (Pi_catd F Z);

rule Pi_elim_funcd (Pi_intro_funcd $C $G $F $CC ) ↪ $CC;

assert [X' : cat] (C : catd X') [X : cat] (G : func X' X) (F : catd X) [Z : catd (Context_cat F)] 
(CC : funcd (Fibre_catd C (Context_elimCat_func (Fibre_catd F G))) (Context_intro_func (Fibre_elim_funcd F G)) Z) ⊢
Pi_elim_funcd (Pi_intro_funcd C G F CC ) ≡ CC;

// //this alternative version has problems to express the rewrite rule (bad, slow)
// constant symbol Pi_elim_funcd_v0 : Π [X : cat] (F : catd X) (Z : catd (Context_cat F)),
// funcd (Fibre_catd (Pi_catd F Z) (Context_elimCat_func F)) Id_func Z;
// type λ [X' : cat] (C : catd X') [X : cat] (G : func X' X) (F : catd X) [Z : catd (Context_cat F)] 
// (CC : funcd (Fibre_catd C (Context_elimCat_func (Fibre_catd F G))) (Context_intro_func (Fibre_elim_funcd F G)) Z)
// [X''] [x' : func X'' X'] [C' : catd X''] [DD : funcd C' x' C] , 
// (Fibre_intro_funcd (Pi_catd F Z) (Context_elimCat_func F) (Context_intro_func (Fibre_elim_funcd F G)) 
//       ((Fibre_elim_funcd C (Context_elimCat_func  ((Fibre_catd F G) )))  ∘>d (Pi_intro_funcd C G F CC)))
//       ∘>d  (Pi_elim_funcd_v0 F Z) 
// = CC;

//naturality

rule @∘>d  _ _ _  $C' $C _  $x' $G $DD (Pi_intro_funcd $C $G $F $CC)
↪ Pi_intro_funcd $C' ($x' ∘> $G) $F 
 ((Fibre_intro_funcd $C (Context_elimCat_func (Fibre_catd $F $G)) (Context_intro_func (Fibre_elim_funcd (Fibre_catd $F $G) $x')) 
      ((Fibre_elim_funcd $C' (Context_elimCat_func  ((Fibre_catd (Fibre_catd $F $G)) $x'))) ∘>d $DD))
      ∘>d $CC);

assert [X' : cat] (C : catd X') [X : cat] (G : func X' X) (F : catd X) [Z : catd (Context_cat F)] 
(CC : funcd (Fibre_catd C (Context_elimCat_func (Fibre_catd F G))) (Context_intro_func (Fibre_elim_funcd F G)) Z)
[X''] [x' : func X'' X'] [C' : catd X''] [DD : funcd C' x' C] ⊢
@∘>d _ _ _  C' C _  x' G DD (Pi_intro_funcd C G F CC)
≡ Pi_intro_funcd C' (x' ∘> G) F 
 ((Fibre_intro_funcd C (Context_elimCat_func (Fibre_catd F G)) (Context_intro_func (Fibre_elim_funcd (Fibre_catd F G) x')) 
      ((Fibre_elim_funcd C' (Context_elimCat_func  ((Fibre_catd (Fibre_catd F G)) x'))) ∘>d DD))
      ∘>d CC);

//TODO: redo naturality for Pi_elim_funcd 
// rule $DD ∘>d (Pi_elim_funcd_v0 $C $G $F $CC) ↪ (Pi_elim_funcd_v0 _ _ $F ($DD ∘>d $CC));


/* -----
* ## TODO: PI-PRODUCT WHEN CARTESIAN FIBRATION (ALONG CARTESIAN OP-FIBRATION) */

// constructions for derived isFibration_con isFibration_cov ...


/*****************************************
* # MODULES (PROFUNCTORS), UNIT HOM MODULES, AND TRANSFORMATIONS,
* YONEDA ACTION
******************************************/

constant symbol mod : Π (A B : cat), TYPE;

constant symbol hom : Π [I A B : cat], func I A → mod A B → func I B → TYPE;
constant symbol hom_type : Π [I A B : cat], func I A → mod A B → func I B → Type;
rule τ (@hom_type $I $A $B $F $R $G) ↪ @hom $I $A $B $F $R $G;

constant symbol transf : Π [A' B' A B: cat], mod A' B' → func A' A → mod A B → func B' B → TYPE;
// when all conversions are in extensional form, this is not used
constant symbol transf_Type : Π [A' B' A B: cat], mod A' B' → func A' A → mod A B → func B' B → Type;
rule τ (@transf_Type $A' $B' $A $B $R' $F $R $G) ↪ @transf $A' $B' $A $B $R' $F $R $G;

symbol <∘ [A B C: cat] : func B C → func A B → func A C ≔ λ G F, F ∘> G;
notation <∘ infix right 90;

/* -----
* ## category/unit hom */

constant symbol Unit_mod : Π [X A B : cat], func A X → func B X → mod A B;

constant symbol Terminal_mod : Π (A B : cat), mod A B;

/* -----
* ## arrows in category/unit hom  */

constant symbol Id_hom : Π [A B : cat] (F : func B A),
hom F (Unit_mod Id_func Id_func ) F;

symbol Func_con_hom : Π [A B A' : cat] (Z : func A A') (F : func B A),
hom F (Unit_mod Z Id_func) (Z <∘ F);

symbol Func_cov_hom : Π [A B A' : cat] (Z : func A A') (F : func B A),
hom (F ∘> Z) (Unit_mod Id_func Z) F;

constant symbol Terminal_hom : Π [A B I : cat] (F : func I A) (G : func I B), hom F (Terminal_mod A B) G;

/* -----
* ## transformations of modules  */

constant symbol Id_transf : Π [A X : cat] (R : mod A X) ,
transf R Id_func R Id_func;

injective symbol Terminal_transf : Π [A B B': cat] (R : mod A B) (G : func B B'), transf R Id_func (Terminal_mod A B') G;

/* -----
* ## pullback/composition/substitution along functors into of modules. part 1 */

//Subst_cov_mod
symbol <<∘ : Π [A X C: cat], mod A X → func C X → mod A C;

//Subst_con_mod
symbol ∘>> : Π [X B C: cat], func C X → mod X B → mod C B;
notation <<∘ infix left 80; notation ∘>> infix right 80;

rule (Unit_mod $F $G) <<∘ $K ↪ Unit_mod $F ($G <∘ $K);

rule $K ∘>> (Unit_mod $F $G) ↪ Unit_mod ($K ∘> $F) $G;

rule $R <<∘ Id_func ↪ $R 
with ($R <<∘ $H) <<∘ $K ↪ $R <<∘ ($H <∘ $K);

rule Id_func ∘>> $R ↪ $R 
with $K ∘>> ($H ∘>> $R) ↪ ($K ∘> $H) ∘>> $R;

rule ($F ∘>> $R) <<∘ $G ↪ ($F ∘>> ($R <<∘ $G));

rule Terminal_mod _ _ <<∘ $H ↪ Terminal_mod _ _
with $H ∘>> Terminal_mod _ _ ↪ Terminal_mod _ _;

/* *** yoneda action (embedding), covariant and contravariant *** */

//Unit_cov_transf
injective symbol ∘>'_ : Π [I A B J : cat] [F : func I A] [R : mod A B] [G : func I B],
hom F R G → Π (N: func J B), transf (Unit_mod G N) F (R <<∘ N) Id_func;

//Unit_con_transf
injective symbol _'∘> : Π [I A B J : cat] [F : func I A] [R : mod A B] [G : func I B],
Π (M : func J A), hom F R G → transf ( Unit_mod M F) Id_func (M ∘>> R) G;

notation _'∘> infix right 80; notation ∘>'_ infix left 80;

/* *** substitution/composition along arrow into a transformation *** */

//Comp_hom
symbol '∘ : Π [A B' B I : cat] [S : mod A B'] [T : mod A B]
[X : func I A] [Y : func I B'] [G : func B' B],
hom X S Y → transf S Id_func T G → hom X T (G <∘ Y);
notation '∘ infix right 80;

symbol ∘' [A' B A I : cat] [S : mod A' B] [T : mod A B]
[X : func I A'] [Y : func I B] [F : func A' A] :
transf S F T Id_func → hom X S Y → hom (X ∘> F) T Y;
notation ∘' infix left 80;

/* *** substitution/composition along transformation into a transformation *** */

symbol ''∘ [ B'' B' A B : cat] [R : mod A B''] [S : mod A B'] [T : mod A B] 
[Y : func B'' B'] [G : func B' B] :
transf R Id_func /*GEN HERE*/ S Y → transf S Id_func T G → transf R Id_func T (G <∘ Y);
// transf R X S Y → transf S Id_func T G → transf R X T (G <∘ Y);
notation ''∘ infix right 80;

symbol ∘'' : Π [A'' A' B A  : cat] [R : mod A'' B] [S : mod A' B] [T : mod A B] 
[X : func A'' A'] [F : func A' A],
transf S F T Id_func → transf R X S Id_func → transf R (X ∘> F) T Id_func;
notation ∘'' infix left 80;

rule $rs ''∘ ($st ''∘ $tu) ↪ ($rs ''∘ $st) ''∘ $tu
with ($tu ∘'' $st) ∘'' $rs ↪ $tu ∘'' ($st ∘'' $rs);

rule $r'r '∘ (Id_transf _) ↪ $r'r
with (Id_transf _) ∘' $r'r ↪ $r'r;

rule (Id_transf _) ''∘ $r'r ↪ $r'r
with $r'r ''∘ (Id_transf _) ↪ $r'r;
rule (Id_transf _) ∘'' $r'r ↪ $r'r
with $r'r ∘'' (Id_transf _) ↪ $r'r;

rule $r '∘ ($rs ''∘ $st)
↪ ($r '∘ $rs) '∘ $st
with ($st ∘'' $rs) ∘' $r
↪ $st ∘' ($rs ∘' $r);

/* *** composition/substitution along functors into module elements/arrows *** */

//Comp_func_hom
symbol ∘↓ : Π [I A B I' : cat] [R : mod A B] [F : func I A] 
[G : func I B], hom F R G → Π (X : func I' I), hom (X ∘> F) R (G <∘ X);
notation ∘↓ infix left 120;

rule $r ∘↓ Id_func ↪ $r
with ($r ∘↓ $H) ∘↓ $K ↪ $r ∘↓ ($K ∘> $H )
with (Id_hom $F) ∘↓ $H ↪ Id_hom ($F <∘ $H)
with (Func_con_hom $Z $F) ∘↓ $H ↪ Func_con_hom $Z ($F <∘ $H)
with (Func_cov_hom $Z $F) ∘↓ $H ↪ Func_cov_hom $Z ($F <∘ $H);

rule ($a '∘  $t) ∘↓ $Z ↪ (($a ∘↓ $Z) '∘  $t)
with ($t ∘' $a) ∘↓ $Z ↪ ($t ∘' ($a ∘↓ $Z)) ;

/* *** accumulation, functoriality, naturality of operations *** */

//accumulation contravariant ; accumulation not really naturality, therefore can be dealt with generically
// t∘(g) ∘X0 -  =  t∘(g ∘X0 -) 
rule ($M)_'∘> ($g '∘ (($X0)_'∘> $t))
↪ (($M)_'∘> $g) ''∘ (($M ∘> $X0)_'∘> $t)

with (($t ∘>'_ ($X0) ∘' $g)) ∘>'_($M)
↪ ($t ∘>'_($M ∘> $X0)) ∘'' ($g ∘>'_($M));

assert [L R J I I' I1 : cat] [T : mod R L]
[Y0 : func I1 R] [Y: func I' I1] [Z : func I1 L]
(M : func J I) [X: func I' I] (X0: func I R) 
(t : hom Y0 T Z)
(g : hom X (Unit_mod X0 Y0) Y) ⊢ eq_refl _ : τ (

(M)_'∘> (g '∘ ((X0)_'∘> t))
= ((M)_'∘> g) ''∘ ((M ∘> X0)_'∘> t) );

//accumulation  covariant ; accumulation not really naturality, therefore can be dealt with generically
 //  - ∘X0 (g)∘t   =  (- ∘X0 g)∘t 
//  rule ($g '∘ ($t ∘>'_($X0))) ∘>'_($M)
// ↪ ($t ∘>'_($X0 <∘ $M)) ∘'' ($g ∘>'_($M));
rule (($t ∘>'_($X0)) ∘' $g) ∘>'_($M)
↪ ($t ∘>'_($X0 <∘ $M)) ∘'' ($g ∘>'_($M));

// naturality part1

//naturality (of func_cov_hom ?)  TOO REVIEW THIS
type  λ [A B  : cat] [R : mod A B]    [y : func A B]
[J1] [G : func J1 B] [I] [y'y : func I J1] [y' : func I A] (y'y_ : hom y' (Unit_mod y G) y'y) 
(s : hom Id_func R y)
[J] [x''x' : func J A] [x'] (x''x'_ : hom x''x' (Unit_mod Id_func y') x') ,
(s ∘>'_(_)) ∘' (x''x'_ '∘ ((Id_func)_'∘> ( y'y_ ))) 
=  (x''x'_ '∘ ((Id_func)_'∘> ( ((∘>'_) [_] [_] [_] [_] [Id_func] s (_)) ∘' y'y_ ))) ;

rule ($x''x'_ '∘ ((Id_func)_'∘> ( ((∘>'_) [_] [_] [_] [_] [Id_func] $s (_)) ∘' $y'y_ ))) 
↪ ($s ∘>'_(_)) ∘' ($x''x'_ '∘ ((Id_func)_'∘> ( $y'y_ ))) ;

//functoriality/naturality covariant     
rule (( ($Y ∘> $Y0)_'∘> (Func_con_hom ($Z_LAdj_func) $N)))
      ''∘ ((@'∘ _ _ _ _ _ _ _ $Y _ $g   (($X0)_'∘> ((Func_con_hom $Z_LAdj_func $Y0)))) ∘>'_(Id_func))
↪ (($g '∘ (($X0)_'∘> (Id_hom $Y0))) ∘>'_($N))
       ''∘ (($X0)_'∘> ((Func_con_hom $Z_LAdj_func $N))) ;

assert  [L I : cat] [Z_LAdj_func : func I L]
  [J I1 I2 : cat] [X0: func J I] [Y: func J I2] [Y0 : func I2 I] 
  [g : hom Id_func (Unit_mod X0 Y0) Y] [J' : cat] [N : func J' I] ⊢ eq_refl _ : τ (
 
  (( (Y ∘> Y0)_'∘> (Func_con_hom (Z_LAdj_func) N)))
  ''∘ ((g '∘ ((X0)_'∘> ((Func_con_hom Z_LAdj_func Y0)))) ∘>'_(Id_func))
 = ((g '∘ ((X0)_'∘> (Id_hom Y0))) ∘>'_(N))
            ''∘ ((X0)_'∘> ((Func_con_hom Z_LAdj_func N))) );
 

/* *** pullback/composition/substitution along functors into of modules. part 2 *** */

constant symbol ∘>>_proj : Π [X Y X' : cat] (F : func X' X) (R : mod X Y), 
transf (F ∘>> R) F R Id_func;

constant symbol ∘>>_intro : Π [X Y X' X'' Y': cat] (F : func X' X) (R : mod X Y) (F' : func X'' X') [G : func Y' Y] [S : mod X'' Y'], 
transf S (F' ∘> F) R G  →
/* G requires general '∘' ? or actual use will have one of F' id or G id */
transf S F' (F ∘>> R) G /* G */;

//extensional... there are reasons for this... (in particular, trying to mix non-id cov and non-id con will require extensional as there is none op composing mixed transf)
rule ( ∘>>_proj $F $R ) ∘' (( ∘>>_intro $F $R $F' $r_ ) ∘' $x) ↪ $r_ ∘' $x ;
// rule ( ∘>>_proj $F $R ) ∘'' ( ∘>>_intro $F $R $F' $r_ ) ↪ $r_ ;

// pullback-of-modules operation is functorially extends to transformations of modules
symbol <<∘1 : Π [X Y X' : cat] [F : func X X'] [R' : mod X' Y] [R : mod X Y] (r : transf R F R' Id_func) [Z : cat] (H : func Z Y), 
transf (R <<∘ H) F (R' <<∘ H) Id_func;
notation <<∘1 infix left 80;

rule ($r ∘>'_($N)) <<∘1 $H ↪ $r ∘>'_($N <∘ $H);
rule $t <<∘1 Id_func ↪ $t 
with ($t <<∘1 $H) <<∘1 $K ↪ $t <<∘1 ($H <∘ $K)
with (Id_transf $R) <<∘1 $K ↪ Id_transf ($R <<∘ $K);

symbol 1∘>> : Π [X Y Y' : cat] [G : func Y Y'] [R' : mod X Y'] [R : mod X Y] [Z : cat] (H : func Z X) (r : transf R Id_func R' G) , 
transf (H ∘>> R) Id_func (H ∘>> R') G;
notation 1∘>> infix right 80;

rule $H 1∘>> (($M) _'∘> $r ) ↪ ($H ∘> $M) _'∘> $r;
rule Id_func 1∘>>  $t ↪ $t 
with $K 1∘>> ($H 1∘>> $t) ↪ ($K ∘> $H) 1∘>> $t
with $K 1∘>> (Id_transf $R) ↪ (Id_transf ($K ∘>> $R));

rule ($F 1∘>> $t) <<∘1 $G ↪ ($F 1∘>> ($t <<∘1 $G));

rule ( ∘>>_proj $H $R' )  ∘' ($x '∘ ( @1∘>> _ _ _ $G $R' $R $Z $H  $r_ ))
 ↪ (( ∘>>_proj $H $R )  ∘' $x ) '∘  $r_ ;

// more conversion rules on identity arrows of functors as profunctors

//TODO replaced this by multiple equations
rule Func_con_hom Id_func $F ↪ (Id_hom $F)
with Func_cov_hom Id_func $F ↪ (Id_hom $F);

rule (Func_cov_hom _ $G ) '∘ ((_) _'∘> Id_hom $F) ↪ Id_hom ($G ∘> $F);
rule (Id_hom $F ∘>'_ (_) ) ∘' (Func_con_hom _ $G ) ↪ Id_hom ($G ∘> $F);
//TODO: REVIEW NECESSITY OF ID_HOM. both cov id and con id without id_hom are ok because would never mix anyway ?
// or maybe formulation where all converge to id noop only in applied form ?
//WARNING slow in transf formulation
//WARNING rule ($M)_'∘> (Id_hom Id_func) ↪ (Id_transf _);
rule ($f '∘ ($M)_'∘> (Id_hom Id_func) ) ↪ $f
with ((Id_hom Id_func) ∘>'_ (_)) ∘' $f ↪ $f;
//TODO review if applied form only
rule $f '∘ (($M)_'∘> (Func_cov_hom $F Id_func) ) ↪ $f;
rule ((Func_con_hom $F Id_func) ∘>'_($M)) ∘' $f ↪ $f;

 // idhom ''∘ funchom = idhom
rule (($M)_'∘> ((Func_con_hom $F $Z)) ) ''∘ (($M ∘> $F)_'∘> (Func_con_hom $F' Id_func)) 
 ↪ (($M)_'∘> ((Func_con_hom ($F ∘> $F') $Z))) ;
 
assert [A B : cat] (F : func B A) B' (Z : func B' B) I (M : func I B) C (F' : func A C) ⊢ eq_refl _ : τ (

 ((M)_'∘> ((Func_con_hom F Z)) ) ''∘ ((M ∘> F)_'∘> (Func_con_hom F' Id_func)) 
 = ((M)_'∘> ((Func_con_hom (F ∘> F') Z))) );
 // : ransf (Unit_mod M (Z ∘> Id_func)) (Id_func ∘> Id_func) ((M ∘> F) ∘>> Unit_mod F' Id_func) (F' <∘ (F <∘ Z))

//yoneda bijection half 1
 // j-rule then applied to id_hom, both cov and con
 //  todo solved, erase this comment: note for confluence that already exists another rewrite that jrule of restr 
rule (((Func_cov_hom $F $Z)) '∘ ((Id_func)_'∘> $r)) 
↪ $r ∘↓ $Z;
//REVIEW: also this rule because confluence question?
rule ($f ∘>'_(_)) ∘' Id_hom $Z ↪ $f ∘↓ $Z
with Id_hom $Z '∘ ((_)_'∘> $f) ↪ $f ∘↓ $Z ;

assert [I A B : cat] [F : func I A] [R : mod A B] [G : func I B]
 (r : hom F R G ) J (Z : func J _ ) ⊢ eq_refl _ : τ (

   (((Func_cov_hom F Z)) '∘ ((Id_func)_'∘> r)) 
 = r ∘↓ Z );

//yoneda bijection half 2
// SOLVED: now can  solve $Z ∘> $dom_t ≡ $Z
rule (Id_func)_'∘> (((Func_cov_hom $Z Id_func)) '∘ $t) 
 ↪ $t;

  assert [B : cat] I (M : func I B) f ⊢ eq_refl _ : τ ( //note as transf fail because reduction to Id_hom
  (f '∘ (M)_'∘> (Func_con_hom Id_func Id_func) )  = f );
  
 //todo: derivable restr ?
 // type λ [A B : cat] (F : func B A) B' (Z : func B' B) I (M : func I B) C (F' : func A C) ,
 // ((M)_'∘> ((Func_con_hom F) ∘↓ Z) ) ;
 
 // id_cov_hom on id_func is id_transf
 //nope todo erase see id_hom
//  rule (($M)_'∘> (Func_con_hom Id_func Id_func) )
// ↪ (Id_transf _);
//  assert [B : cat] I (M : func I B) ⊢ eq_refl _ : τ (
//  ((M)_'∘> (Func_con_hom Id_func Id_func) )
//  = (Id_transf (Unit_mod M Id_func)) );


/*****************************************
* # CUT-ELIMINATION AND ASSOCIATIVITY METATHEOREM
******************************************/

// See Kosta Dosen's "Cut-elimination in categories"

// it is a metatheorem by cases induction that the associativity propositional-equation is derivable,
// and it must not be assumed as rewrite/conversion rule
constant symbol associativity_con_metatheorem : Π [A B I : cat] [R : mod A B] [x : func I A] [y : func I B],
Π [J1] [G : func J1 B] [y'y : func I J1] (y'y_ : hom Id_func (Unit_mod y G) y'y) ,
Π (s : hom x R y), 
Π [K0] [F' : func K0 A] [x''x' : func I K0] (x''x'_ : hom x''x' (Unit_mod F' x) Id_func) , 
τ (( (( x''x'_ '∘ ( (F')_'∘> s) ) ∘>'_(G)) ∘' y'y_ ) 
  =  (x''x'_ '∘ ((F')_'∘> ( (s ∘>'_(G)) ∘' y'y_ ))));


/*****************************************
* # PRODUCT CATEGORY
******************************************/

injective symbol Product_cat : Π (U : cat) (A : cat), cat;

symbol Product_projL_func : Π [A1 A2 B: cat], func B (Product_cat A1 A2) → func B A1 ;
symbol Product_projR_func : Π [A1 A2 B: cat], func B (Product_cat A1 A2) → func B A2 ;
injective symbol Product_pair_func : Π [A1 A2 I : cat] (F : func I A1) (G : func I A2),
  func I (Product_cat A1 A2);

// naturality
rule $H ∘> (Product_pair_func $F $G) ↪ (Product_pair_func ($H ∘> $F) ($H ∘> $G))
with $H ∘> (Product_projL_func $F) ↪ (Product_projL_func ($H ∘> $F))
with $H ∘> (Product_projR_func $F) ↪ (Product_projR_func ($H ∘> $F));

// beta
rule (Product_projL_func (Product_pair_func $F $G)) ↪ $F 
with (Product_projR_func (Product_pair_func $F $G)) ↪ $G;

// eta
rule Product_pair_func (Product_projL_func $F) (Product_projR_func $F) ↪ $F;

// convenient shortcuts
rule Product_cat Terminal_cat $A ↪ $A
with Product_cat $A Terminal_cat ↪ $A;
rule @Product_projL_func Terminal_cat $A _ $F ↪ Terminal_func _
with @Product_projR_func Terminal_cat $A _ $F ↪ $F 
with @Product_pair_func Terminal_cat $A _  $F $G ↪ $G
with @Product_projL_func $A Terminal_cat _ $F ↪ $F
with @Product_projR_func $A Terminal_cat _ $F ↪ Terminal_func _
with @Product_pair_func $A Terminal_cat _  $F $G ↪ $F;

//TODO: REVIEW: IS SIMPLIFIED VERSION WITHOUT EXTRA INNER PARAMS N1 N2 ENOUGH ?
// see Product_pair_cov_hom_simple version below
injective symbol Product_pair_cov_hom : Π [A1 A2 I : cat] [J] [F' : func J A1] [G' : func J A2] [K] (X : func I K) [K'1] (M1 : func K K'1) [N1 : func K'1 A1] [K'2] (M2 : func K K'2) [N2 : func K'2 A2]  (Y : func I J) ,
hom (X ∘> M1) (Unit_mod N1 F') Y → 
hom (X ∘> M2) (Unit_mod N2 G') Y →
hom X (Unit_mod (Product_pair_func (M1 ∘> N1) (M2 ∘> N2)) (Product_pair_func F' G')) Y;

rule (Func_cov_hom (Product_projL_func Id_func) _ ) ∘>'_(_) ∘' (Product_pair_cov_hom $X $M1 $M2 $Y $h1 $h2) ↪ ((Id_hom _) ∘>'_(_)) ∘' $h1;
rule (Func_cov_hom (Product_projR_func Id_func) _ ) ∘>'_(_) ∘' (Product_pair_cov_hom $X $M1 $M2 $Y $h1 $h2) ↪ ((Id_hom _) ∘>'_(_)) ∘' $h2;

injective symbol Product_pair_con_hom : Π [A1 A2 I : cat] [J] [F' : func J A1] [G' : func J A2] [K] (X : func I K) [K'1] (M1 : func K K'1) [N1 : func K'1 A1] [K'2] (M2 : func K K'2) [N2 : func K'2 A2]  (Y : func I J) ,
hom Y (Unit_mod F' N1) (X ∘> M1) → 
hom Y (Unit_mod G' N2) (X ∘> M2) →
hom Y (Unit_mod (Product_pair_func F' G') (Product_pair_func (M1 ∘> N1) (M2 ∘> N2))) X;

rule (Product_pair_con_hom $X $M1 $M2 $Y $h1 $h2) '∘  (_)_'∘>  (Func_con_hom (Product_projL_func Id_func) _ ) ↪ $h1 '∘ ((_)_'∘> (Id_hom _));
rule (Product_pair_con_hom $X $M1 $M2 $Y $h1 $h2) '∘  (_)_'∘>  (Func_con_hom (Product_projR_func Id_func) _ ) ↪ $h2 '∘ ((_)_'∘> (Id_hom _));

injective symbol Product_pair_cov_hom_simple : Π [A1 A2 I : cat] [J] [F' : func J A1] [G' : func J A2]  [X : func I _] [X']  [Y : func I J] ,
hom X (Unit_mod Id_func F') Y → 
hom X' (Unit_mod Id_func G') Y →
hom (Product_pair_func X X') (Unit_mod Id_func (Product_pair_func F' G')) Y  
≔ begin
  assume A1 A2 I J F' G' X X' Y h1 h2;
  refine (@Product_pair_cov_hom _ _ _ _ _ _ _ _   _ (Product_projL_func Id_func) Id_func _ (Product_projR_func Id_func) Id_func  _ h1 h2);
end ;

/* -----
* ## ADDITIONAL DEFINABLE SYMBOLS*/

// (definable) operaton used in carterSolution15.lp for 1+2=3
// not really optional symbol, because injective keyword...
injective symbol Product_mapR_func : Π (A : cat) [B B' : cat] (F : func B B'), func (Product_cat A B) (Product_cat A B'); 
rule Product_mapR_func $A $G ↪ Product_pair_func (Product_projL_func Id_func) (Product_projR_func Id_func ∘> $G); 

// DO NOT ERASE, FOR REFERENCE. 
// THESE RULES ARE DERIVABLE:
assert (A : cat) [B B' : cat] (F : func B B') B'' (F' : func B' B'') ⊢
(Product_mapR_func A F) ∘> (Product_mapR_func A F') ≡ (Product_mapR_func A (F ∘> F'));
assert (A : cat) [B  : cat]  ⊢
 (Product_mapR_func A (@Id_func B)) ≡ Id_func;
// rule (Product_mapR_func $A $F) ∘> (Product_mapR_func $A $G) 
// ↪ (Product_mapR_func $A ($F ∘> $G))
// with (Product_mapR_func $A Id_func) ↪ Id_func ;

// DO NOT ERASE, FOR REFERENCE. 
// THESE RULES ARE DERIVABLE:
assert (A : cat) [B B' : cat] (F : func B B') ⊢
(Product_projL_func (Product_mapR_func A F) ) ≡ (Product_projL_func Id_func);
assert [A1 A2 I : cat] (F : func I A1) (G : func I A2) A2' (K : func A2 A2') ⊢
Product_pair_func F G ∘> (Product_mapR_func _ K) ≡ Product_pair_func F (G ∘> K);
// rule (Product_projL_func (Product_mapR_func $A $F) ) ↪ (Product_projL_func Id_func);
// rule (Product_projR_func (Product_mapR_func $A $F)) ↪ (Product_projR_func Id_func) ∘> $F;
// rule (@Product_pair_func _ _ _ $F $G) ∘> (@Product_mapR_func _ _ _ $K) ↪ (@Product_pair_func _ _ _  $F ($G ∘> $K));

// injective symbol Product_pair_cov_hom_simple : Π [A1 A2 I : cat] [J] [F' : func J A1] [G' : func J A2] [K] (X : func I K) (M1 : func K A1)  (M2 : func K A2)  (Y : func I J) ,
// hom (X ∘> M1) (Unit_mod Id_func F') Y → 
// hom (X ∘> M2) (Unit_mod Id_func G') Y →
// hom X (Unit_mod (Product_pair_func (M1 ) (M2 )) (Product_pair_func F' G')) Y  
// ≔ begin  ;

injective symbol Product_mapR_con_hom [A1 A2 I : cat] [G : func I A2] /* [J] */ [G' : func I A2] /* [Y] */
(h : hom G (Unit_mod Id_func G') Id_func) :
hom (Product_mapR_func A1 G) (Unit_mod Id_func (Product_mapR_func A1 G'))  Id_func
≔ begin 
  assume A1 A2 I G G' h; simplify;
  refine (Product_pair_cov_hom_simple 
    (Func_cov_hom (Product_projL_func Id_func) Id_func) 
    (h ∘>'_(_) ∘' (Func_cov_hom (Product_projR_func Id_func) Id_func)));
end;

// DO NOT ERASE, FOR REFERENCE. 
// RULE IS DERIVABLE:
assert [A1 A2 I : cat] [G : func I A2] /* [J] */ [G' : func I A2] /* [Y] */
(h : hom G (Unit_mod Id_func G') Id_func) ⊢
(Func_cov_hom (Product_projR_func Id_func) _ ) ∘>'_(_) ∘'  (Product_mapR_con_hom h )
≡ (h ∘>'_ Product_projR_func Id_func) ∘' Func_cov_hom (Product_projR_func Id_func) Id_func;
// rule (Func_cov_hom (Product_projR_func Id_func) _ ) ∘>'_(_) ∘' (Product_mapR_con_hom $h )
//     ↪ $h ∘>'_(_) ∘' (Func_cov_hom (Product_projR_func Id_func) _ ) ;
// rule (Func_cov_hom (Product_projL_func Id_func) _ ) ∘>'_(_) ∘' (Product_mapR_con_hom $h )
//     ↪  (Func_cov_hom (Product_projL_func Id_func) _ ) ;


/*****************************************
* # PRODUCT CATEGORY AS A TRIVIAL ISOFIBRATION
******************************************/

injective symbol Trivial_catd : Π (U : cat) (A : cat), catd U;
rule Trivial_catd $U Terminal_cat ↪ Terminal_catd _;

constant symbol Trivial_intro_funcd : Π [U A V : cat] (F : func V U) (G : func V A), 
funcd (Terminal_catd V) F (Trivial_catd U A);

constant symbol Trivial_base_funcd : Π [U A V : cat] (Z : func U V), 
funcd (Trivial_catd U A) Z (Trivial_catd V A);

rule Trivial_intro_funcd $F $G ∘>d Trivial_base_funcd $Z ↪ Trivial_intro_funcd ($F ∘> $Z) $G;
rule Trivial_base_funcd $Z ∘>d Trivial_base_funcd $Z' ↪ Trivial_base_funcd ($Z ∘> $Z');

rule Context_cat (Trivial_catd $U $A) ↪ Product_cat $U $A;

rule Context_elimCat_func (Trivial_catd $U $A) ↪ @Product_projL_func $U $A _ Id_func ;

rule Context_elimCatd_funcd (Trivial_catd $U $A) ↪ 
 Trivial_intro_funcd (@Product_projL_func $U $A _ Id_func) (@Product_projR_func $U $A _ Id_func) ;

rule Context_intro_func (Trivial_intro_funcd $F $G) ↪ Product_pair_func $F $G;


/*****************************************
* # INDUCTIVE DATA TYPE, EXAMPLE OF THE JOIN CATEGORY
******************************************/

//TODO: dependent eliminatioon, for now only the recursor is done

symbol join_cat : Π (A B : cat), cat;
symbol join_fst_func : Π (A B : cat), func A (join_cat A B);
symbol join_snd_func : Π (A B : cat), func B (join_cat A B);
symbol join_hom :  Π (A B : cat) [I : cat] (a : func I A) (b : func I B), hom a (Unit_mod (join_fst_func A B) (join_snd_func A B)) b ;

rule @'∘ _ _ _ _ _ _ $a' Id_func _ $r (( Id_func ) _'∘> (join_hom $A $B $a $b)) ↪ (join_hom $A $B $a' $b);
assert (A B : cat) [I : cat] (a : func I A) (b : func I B) [a'] (r : hom a' (Unit_mod Id_func a) Id_func) ⊢ 
        eq_refl _  : τ (r  '∘ (( _ ) _'∘> (join_hom A B a b)) = (join_hom A B a' b));

symbol join_elim_con_func : Π (A B : cat) [E : cat] (first_func : func A E) (second_func : func B E) 
(one_hom : Π (I : cat) (a : func I A) (b : func I B), hom a (Unit_mod (first_func) Id_func) (second_func <∘ b)) //note extensionality second_func outside
(natural_eq : Π [I : cat] (a : func I A) (b : func I B) [a'] (r : hom a' (Unit_mod Id_func a) Id_func) , 
      τ (r  '∘ (( _ ) _'∘> (one_hom I a b)) = (one_hom I a' b))), 
  func (join_cat A B) E;

rule join_fst_func $A $B ∘> (join_elim_con_func $A $B $F0 $F1 $r _) ↪ $F0
with join_snd_func $A $B ∘> (join_elim_con_func $A $B $F0 $F1 $r _) ↪ $F1;


rule ((join_hom $A $B $a $b) '∘ ((join_fst_func $A $B) _'∘> (Func_con_hom (join_elim_con_func $A $B $first_func $second_func $one_hom _) 
              (join_snd_func $A $B)))) ↪ $one_hom _ $a $b ;

assert (A B : cat) [E : cat] (first_func : func A E) (second_func : func B E) 
(one_hom : Π (I : cat) (a : func I A) (b : func I B), hom a (Unit_mod (first_func) Id_func) (second_func <∘ b))
[I : cat] (a : func I A) (b : func I B) ⊢ eq_refl _ : τ (

((join_hom A B a b) '∘ ((join_fst_func A B) _'∘> (Func_con_hom (join_elim_con_func A B first_func second_func one_hom _) 
                            (join_snd_func A B)))) = one_hom _ a b );


/*****************************************
* # DEPENDENT (ISO)FIBRATIONS OF MODULES
******************************************/

constant symbol modd : Π [X Y : cat], catd X → mod X Y → catd Y → TYPE;

constant symbol homd : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y], hom F R G → 
Π [A : catd X] [B : catd Y] [II : catd I] (FF : funcd II F A) (RR : modd A R B) (GG : funcd II G B), TYPE;
constant symbol homd_type : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y], hom F R G → 
Π [A : catd X] [B : catd Y] [II : catd I] (FF : funcd II F A) (RR : modd A R B) (GG : funcd II G B), Type;
rule τ (@homd_type $X $Y $I $F $R $G $r $A $B $II $FF $RR $GG) ↪ @homd $X $Y $I $F $R $G $r $A $B $II $FF $RR $GG;

constant symbol transfd : Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [F : func X X'] [G : func Y Y'] [R' : mod X' Y'] [R : mod X Y]
(r : transf R F R' G) (RR: modd A R B) (FF : funcd A F A') (RR' : modd A' R' B') (GG : funcd B G B'), TYPE;

// modules

constant symbol Unit_modd : Π [I X Y : cat] [xi : func X I] [yi : func Y I] 
[XX : catd X] [YY : catd Y] [II : catd I] (F : funcd XX xi II) (G : funcd YY yi II), 
modd XX (Unit_mod xi yi) YY;

constant symbol Terminal_modd : Π [X Y : cat] (R : mod X Y) ,
 modd (Terminal_catd X) R (Terminal_catd Y);
 
symbol Fibre_transf_modd : Π [X Y X' Y' : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 (RR : modd A R B) [S : mod X' Y'] [x : func X' X] [y : func Y' Y], transf S x R y → 
  modd (Fibre_catd A x) S (Fibre_catd B y);
 
rule Fibre_transf_modd $A (Id_transf _) ↪ $A
with Fibre_transf_modd $A ($x ''∘ $y) ↪ Fibre_transf_modd (Fibre_transf_modd $A $y) $x
with Fibre_transf_modd $A ($y ∘'' $x) ↪ Fibre_transf_modd (Fibre_transf_modd $A $y) $x
with Fibre_transf_modd (Terminal_modd _) $F ↪ Terminal_modd _ ;
 
symbol d<<∘ : Π [A B : cat] [AA : catd A] [BB : catd B] [R : mod A B], modd AA R BB → Π [B' : cat] [b : func B' B] [BB' : catd B'], funcd BB' b BB → modd AA (R <<∘ b) BB'; 
notation d<<∘ infix left 80; //Subst_cov_modd

symbol ∘>>d : Π [A B : cat] [AA : catd A] [BB : catd B] [R : mod A B], Π [A' : cat] [a : func A' A] [AA' : catd A'], funcd AA' a AA → modd AA R BB → modd AA' (a ∘>> R) BB;
notation ∘>>d infix right 80; //Subst_con_modd
 
symbol d<∘ [X Y Z : cat] [A : catd X] [B : catd Y] [C : catd Z] [F : func X Y]
[G : func Y Z] : funcd B G C → funcd A F B → funcd A (F ∘> G) C ≔ λ G F, F ∘>d G;
notation d<∘ infix right 90;
  
rule $R d<<∘ Id_funcd ↪ $R 
// with $R d<<∘ ($H d<∘ $K) ↪ ($R d<<∘ $H) d<<∘ $K;
  with ($R d<<∘ $H) d<<∘ $K ↪ $R d<<∘ ($H d<∘ $K);
 
rule Id_funcd ∘>>d $R ↪ $R 
// with ($K ∘>d $H) ∘>>d $R ↪ $K ∘>>d ($H ∘>>d $R);  
  with $K ∘>>d ($H ∘>>d $R) ↪ ($K ∘>d $H) ∘>>d $R;
 
rule ($F ∘>>d $R) d<<∘ $G ↪ ($F ∘>>d ($R d<<∘ $G));

rule (Unit_modd $F $G) d<<∘ $K ↪ Unit_modd $F ($G d<∘ $K) 
with $K ∘>>d (Unit_modd $F $G) ↪ Unit_modd ($K ∘>d $F) $G ;

// elements/arrows of modules

constant symbol Id_homd : Π [I X : cat] [xi : func X I] [II : catd I] [XX] (F : funcd XX xi II) ,
homd  (Id_hom xi) F (Unit_modd Id_funcd Id_funcd) F;

constant symbol Func_con_homd : Π [I X : cat] [F : func X I] [II : catd I] 
 [I'] [II'] [Z : func I I'] (ZZ : funcd II Z II') [XX] (FF : funcd XX F II),
homd  (Func_con_hom Z F)   FF (Unit_modd ZZ Id_funcd) (FF ∘>d ZZ) ;

constant symbol Func_cov_homd : Π [I X : cat] [xi : func X I] [II : catd I] 
 [I'] [II'] [Z : func I I'] (ZZ : funcd II Z II') [XX] (FF : funcd XX xi II),
homd  (Func_cov_hom Z xi) (FF ∘>d ZZ) (Unit_modd Id_funcd ZZ) FF ;

 //Comp_funcd_homd
symbol ∘↓d : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
  [A : catd X] [B : catd Y] [II] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B], 
  homd r FF RR GG → Π [I'] [Z : func I' I] [I'I'] (ZZ : funcd I'I' Z II) ,
  homd (r ∘↓ Z) (ZZ ∘>d FF) RR (ZZ ∘>d GG);
 notation ∘↓d infix left 120;
 
rule $r ∘↓d Id_funcd ↪ $r
 // with $r ∘↓d ($K ∘> $H ) ↪ ($r ∘↓d $H) ∘↓d $K
with ($r ∘↓d $H) ∘↓d $K ↪ $r ∘↓d ($K ∘>d $H )
with (Id_homd $F) ∘↓d $H ↪ Id_homd ($F d<∘ $H)
with (Func_con_homd $Z $F) ∘↓d $H ↪ Func_con_homd $Z ($F d<∘ $H)
with (Func_cov_homd $Z $F) ∘↓d $H ↪ Func_cov_homd $Z ($F d<∘ $H);
 

// transformations of modules

constant symbol Id_transfd : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y] (RR : modd A R B),
 transfd (Id_transf R) RR Id_funcd RR Id_funcd;

symbol _'∘>d : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
[A : catd X] [B : catd Y] [II] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B], 
Π [J: cat] [M : func J X] [JJ : catd J] (MM : funcd JJ M A), 
homd r FF RR GG → transfd ((M)_'∘> r) (Unit_modd MM FF) Id_funcd (MM ∘>>d RR) GG;
notation _'∘>d infix right 80; //unit_con_transfd

symbol ∘>d'_ : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
[A : catd X] [B : catd Y] [II] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B], 
homd r FF RR GG → Π [J: cat] [M : func J Y] [JJ : catd J] (MM : funcd JJ M B), 
transfd ( r ∘>'_(M) ) (Unit_modd GG MM) FF (RR d<<∘ MM ) Id_funcd;                
notation ∘>d'_ infix left 80;
 
symbol '∘d : Π [A'' B' A B : cat] [S : mod A B'] [T : mod A B] 
[X : func A'' A] [Y : func A'' B'] [G : func B' B],
Π [BB' : catd B'] [AA : catd A] [BB : catd B] [SS : modd AA S BB'] [TT : modd AA T BB] [t : transf S Id_func T G]
[A''A''] [XX : funcd A''A'' X AA] [YY : funcd A''A'' Y BB'] [GG : funcd BB' G BB] [s : hom X S Y],
homd s XX SS YY → transfd t SS Id_funcd TT GG → homd (s '∘ t) XX TT (YY ∘>d GG);
notation '∘d infix right 80;  //comp_homd_transfd

symbol ∘d' [A'' A'  A B : cat] [S : mod A' B] [T : mod A B] 
[X : func A'' A'] [Y : func A'' B] [F : func A' A] 
[AA' : catd A'] [AA : catd A] [BB : catd B] [SS : modd AA' S BB] [TT : modd AA T BB] [t : transf S F T Id_func]
[A''A''] [XX : funcd A''A'' X AA'] [YY : funcd A''A'' Y BB] [FF : funcd AA' F AA] [s : hom X S Y]:
transfd t SS FF TT Id_funcd → homd s XX SS YY → homd (t ∘' s) (XX ∘>d FF) TT YY;
notation ∘d' infix left 80;

//TODO: REVIEW //SEE RULE somewhere in reverse. already solved..? //reverse?
rule ($a '∘d  $t) ∘↓d $Z ↪ (($a ∘↓d $Z) '∘d  $t)
with ($t ∘d' $a) ∘↓d $Z ↪ ($t ∘d' ($a ∘↓d $Z)) ;

symbol ''∘d : Π [B'' B' A B : cat] [R : mod A B''] [S : mod A B'] [T : mod A B] 
 [Y : func B'' B'] [G : func B' B],
Π [BB'' : catd B''] [BB' : catd B'] [AA : catd A] [BB : catd B] [s : transf R Id_func S Y] [RR : modd AA R BB''] [t : transf S Id_func T G] [SS : modd AA S BB'] [TT : modd AA T BB] 
 [YY : funcd BB'' Y BB'] [GG : funcd BB' G BB],
transfd s RR Id_funcd SS YY → transfd t SS Id_funcd TT GG → 
transfd (s ''∘ t) RR Id_funcd TT (YY ∘>d GG);
notation ''∘d infix right 80; //comp_transfd

symbol ∘d'' : Π [A'' A' A B : cat] [R : mod A'' B] [S : mod A' B] [T : mod A B] 
[X : func A'' A'] [F : func A' A] ,
Π [AA'' : catd A''] [AA' : catd A'] [AA : catd A] [BB : catd B] [s : transf R X S Id_func] [RR : modd AA'' R BB] [t : transf S F T Id_func] [SS : modd AA' S BB] [TT : modd AA T BB] 
[XX : funcd AA'' X AA'] [FF : funcd AA' F AA] ,
transfd t SS FF TT Id_funcd → transfd s RR XX SS Id_funcd → transfd (t ∘'' s) RR (XX ∘>d FF) TT Id_funcd;
notation ∘d'' infix left 80;

rule $rs ''∘d ($st ''∘d $tu) ↪ ($rs ''∘d $st) ''∘d $tu
with ($tu ∘d'' $st) ∘d'' $rs ↪ $tu ∘d'' ($st ∘d'' $rs);

rule (Id_transfd _) ''∘d $r'r ↪ $r'r
with $r'r ''∘d (Id_transfd _) ↪ $r'r;
rule (Id_transfd _) ∘d'' $r'r ↪ $r'r
with $r'r ∘d'' (Id_transfd _) ↪ $r'r;

// assoc comp_transf then comp_hom //reverse?
rule $r '∘d ($rs ''∘d $st)
↪ ($r '∘d $rs) '∘d $st
with ($st ∘d'' $rs) ∘d' $r
↪ $st ∘d' ($rs ∘d' $r);

rule (Func_cov_homd _ $G ) '∘d ((_) _'∘>d Id_homd $F) ↪ Id_homd ($G ∘>d $F);
rule (Id_homd $F ∘>d'_ (_) ) ∘d' (Func_con_homd _ $G ) ↪ Id_homd ($G ∘>d $F);
rule ($f '∘d ($M)_'∘>d (Id_homd Id_funcd) ) ↪ $f
with ((Id_homd Id_funcd) ∘>d'_ (_)) ∘d' $f ↪ $f;
//TODO review if applied form only
rule $f '∘d (($M)_'∘>d (Func_cov_homd $F Id_funcd) ) ↪ $f;
rule ((Func_con_homd $F Id_funcd) ∘>d'_($M)) ∘d' $f ↪ $f;
 
//yoneda bijection half
rule (((Func_cov_homd $F $Z)) '∘d ((Id_funcd)_'∘>d $r)) 
↪ $r ∘↓d $Z;

//yoneda bijection half
rule (Id_funcd)_'∘>d (((Func_cov_homd $Z Id_funcd)) '∘d $t) 
↪ $t;

 // t∘(g) ∘X0 -  =  t∘(g ∘X0 -) 
rule ($M)_'∘>d ($g '∘d (($X0)_'∘>d $t))
 ↪ (($M)_'∘>d $g) ''∘d (($M ∘>d $X0)_'∘>d $t)
with (($t ∘>'_ ($X0) ∘' $g)) ∘>'_($M)
 ↪ ($t ∘>'_($M ∘> $X0)) ∘'' ($g ∘>'_($M));


// fibres of fibred profunctors 

symbol Fibre_modd : Π [X Y X' Y' : cat] [A : catd X] [R : mod X Y] [B : catd Y]
(RR : modd A R B) [S : mod X' Y'] [x : func X' X] [y : func Y' Y], transf S x R y → 
 modd (Fibre_catd A x) S (Fibre_catd B y);

rule Fibre_modd $A (Id_transf _) ↪ $A
with Fibre_modd $A ($x ''∘ $y) ↪ Fibre_modd (Fibre_modd $A $y) $x
with Fibre_modd $A ($y ∘'' $x) ↪ Fibre_modd (Fibre_modd $A $y) $x
with Fibre_modd (Terminal_modd _) $F ↪ Terminal_modd _ ;

injective symbol Fibre_elim_transfd : Π [X Y X' Y' : cat] [A : catd X] [R : mod X Y] [B : catd Y]
(RR : modd A R B) [S : mod X' Y']   [x : func X' X] [y : func Y' Y] (t: transf S x R y) ,
transfd t (Fibre_modd RR t) (Fibre_elim_funcd A x) RR (Fibre_elim_funcd B y);

//TODO: correct and finish
//  injective symbol Fibre_modd_intro_transfd : Π [X Y Y' : cat] [A : catd X] [R : mod X Y] [B : catd Y]
// (RR : modd A R B) [S : mod X Y'] [y : func Y' Y] (t: transf S Id_func R y) ,
// Π [Y0] [y0 : func Y0 Y'] [B0 : catd Y0] [R0 : mod X Y0]  (t0: transf R0 Id_func S y0) [RR0 : modd A R0 B0] [GG] , 
// transfd (t0 ''∘ t) RR0 Id_funcd RR GG 
// → transfd t0 RR0 Id_funcd (Fibre_modd RR t) (Fibre_intro_funcd B y y0 GG) ;

// rule (Fibre_modd_intro_transfd $RR $t $t0 $rr) ''∘d (Fibre_modd_elim_transfd $RR $t) ↪ $rr ;


/* -----
* ## product of (fibred) profunctors */

//TODO: formulate this generally correctly and finish
constant symbol product_modd : Π [A B :  cat] [AA : catd A] [BB : catd B] [S : mod A B] (R R' : modd AA S BB ), modd AA S BB;
constant symbol product_projL_transfd : Π [A B :  cat] [AA : catd A] [BB : catd B] [S : mod A B] (R R' : modd AA S BB ), transfd (Id_transf _) (product_modd R R') Id_funcd R Id_funcd ;


/*****************************************
* # CONTEXT EXTENSION FOR MODULES (PROFUNCTORS)
******************************************/

injective symbol Terminal_transfd : Π [X Y X' Y': cat] [x : func X X'] [y : func Y Y'] [R' : mod X' Y'] [R : mod X Y] [A : catd X] [B : catd Y] (RR : modd A R B)
(t : transf R x R' y ),
 transfd t RR (Terminal_funcd _ _) (Terminal_modd R') (Terminal_funcd _ _);

rule (Terminal_transfd (Terminal_modd _) $rr) ↪ Fibre_elim_transfd (Terminal_modd _) $rr;

rule ($tt ''∘d (Terminal_transfd $RR $t)) ↪ (Terminal_transfd _ _) ;
rule (Terminal_transfd (Terminal_modd _) (Id_transf _)) ↪ (Id_transfd _); // confluent

injective symbol Context_mod : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y],
modd A R B → mod (Context_cat A) (Context_cat B);

rule Context_mod (Terminal_modd $R) ↪ $R
with Context_mod (Unit_modd $FF $GG) ↪ (Unit_mod (Context_intro_func $FF) (Context_intro_func $GG));

injective symbol Context_elimMod_transf : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y] (RR : modd A R B), 
transf (Context_mod RR) (Context_elimCat_func A) R (Context_elimCat_func B);

rule Context_elimMod_transf (Terminal_modd $R) ↪ (Id_transf _);
//TODO: REVIEW: reverse?
rule (@Context_intro_func _ _ (Terminal_catd _) _ _ $FF)_'∘> Func_con_hom (Context_elimCat_func _) Id_func
↪ Context_elimMod_transf (@Unit_modd _ _ _ _ _ (Terminal_catd _) _ _ $FF Id_funcd) ;
// transf (Context_mod (Unit_modd FF Id_funcd)) Id_func (Unit_mod F Id_func) (Context_elimCat_func A);

//TODO: second projection
// injective symbol Context_mod_elimModd_transfd : 

injective symbol Context_intro_hom : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] (r : hom F R G), 
Π [A : catd X] [B : catd Y] [II : catd I] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B],
homd r FF RR GG → hom (Context_intro_func FF) (Context_mod RR) (Context_intro_func GG);

rule (@Context_intro_hom _ _ _ _ _ _  $r  _ _ _  (Fibre_elim_funcd (Terminal_catd _) _)  _ _ $rr) '∘ (Context_elimMod_transf $RR)
↪ $r;

injective symbol Context_intro_transf: Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [F : func X X'] [G : func Y Y'] [R' : mod X' Y'] [R : mod X Y] [r : transf R F R' G] [RR: modd A R B] [FF : funcd A F A'] [RR' : modd A' R' B'] [GG : funcd B G B'],
 transfd r RR FF RR' GG
 → transf (Context_mod RR) (Context_intro_func FF) (Context_mod RR') (Context_intro_func GG);

//TODO: ?relate Context_intro_transf with Context_intro_hom with yoneda

rule Context_intro_transf (Id_transfd _) ↪ Id_transf _
//TODO: generalize (Terminal_catd _) after general ''∘
with Context_intro_transf (@Terminal_transfd _ _ _ _  Id_func _  _ _  (Terminal_catd _) _  $RR $r_) ↪ Context_elimMod_transf $RR ''∘ $r_
with Context_intro_transf (@Terminal_transfd _ _ _ _  _ Id_func  _ _  _ (Terminal_catd _)  $RR $r_) ↪ $r_ ∘'' Context_elimMod_transf $RR;

//TODO: generalize (Terminal_catd _) after general ''∘
//REVIEW: is extensional (applied hom) formulation necessary?
rule (@Context_intro_transf _ _ _ _  (Terminal_catd _) (Terminal_catd _) _ _  (Id_func) _ _ _  $t_ $RR _ $RR' _ $tt_) ''∘ (Context_elimMod_transf $RR') 
↪ (Context_elimMod_transf $RR) ''∘ $t_;

rule (@Context_intro_transf _ _ _ _  _ _ _ _  _ _ _ _  $t_ $RR Id_funcd $RR' _ $tt_) ''∘ (@Context_intro_transf _ _ _ _  _ _ _ _  _ _ _ _  _ _ Id_funcd _ _ $ss_)
↪ (Context_intro_transf ($tt_ ''∘d $ss_ ));

rule (Context_intro_func $FF) ∘>> (Context_mod $RR) ↪ Context_mod ($FF ∘>>d $RR) 
with (Context_mod $RR) <<∘ (Context_intro_func $GG) ↪ Context_mod ($RR d<<∘ $GG );

//REVIEW: was the problem of a general version of naturality for any transf solved
// or is it required to add instances?
//DO NOT ERASE YET, LEAVE COMMENTED
// rule $x '∘ ( (Id_func)_'∘> ($g '∘ Context_elimMod_transf _))
// ↪ $x '∘ (((Id_func)_'∘> $g) ''∘ Context_elimMod_transf _ );


/*****************************************
* # SIGMA-SUM AND PI-PRODUCT OF FIBRED PROFUNCTORS
******************************************/

// ... SIMPLIFIED version
injective symbol Sigma_modd : Π [X Y : cat] [R : mod X Y] (RR : modd (Terminal_catd X) R (Terminal_catd Y)) (ZZ : modd (Terminal_catd X) (Context_mod RR) (Terminal_catd Y)), modd (Terminal_catd X) R (Terminal_catd Y);

constant symbol Sigma_intro_transfd : Π [X Y : cat] [R : mod X Y] (RR : modd (Terminal_catd X) R (Terminal_catd Y)) (ZZ : modd (Terminal_catd X) (Context_mod RR) (Terminal_catd Y)),
    transfd (Context_elimMod_transf RR) ZZ Id_funcd (Sigma_modd RR ZZ) Id_funcd /* (Terminal_funcd _ _) */ ;

constant symbol Sigma_elim_transfd : Π [X Y : cat] [R : mod X Y] (RR : modd (Terminal_catd X) R (Terminal_catd Y)) [ZZ : modd (Terminal_catd X) (Context_mod RR) (Terminal_catd Y)], Π [R'] (t : transf R Id_func R' Id_func) [RR' : modd (Terminal_catd X) R' (Terminal_catd Y)],
transfd ((Context_elimMod_transf RR) ''∘ t) ZZ Id_funcd RR' Id_funcd 
→ transfd t (Sigma_modd RR ZZ) Id_funcd RR' Id_funcd ;

rule (Sigma_intro_transfd $RR $ZZ) ''∘d (Sigma_elim_transfd $RR $t $rr') ↪ $rr';


/* -----
* ## TODO: FULLY GENERAL SIGMA/PI CONSTRUCTIONS ON FIBRED PROFUNCTORS */

//TODO: MORE GENERAL VERSIONS...
// Note that it is not using sigma of categories, it is more general
injective symbol Sigma_modd' : Π [X Y : cat] [R : mod X Y] [YY : catd Y] (RR : modd (Terminal_catd X) R YY) [YY0 : catd (Context_cat YY)] (ZZ : modd (Terminal_catd X) (Context_mod RR) YY0) [YY1 : catd Y] (GG : funcd YY0 (Context_elimCat_func YY) YY1) , modd (Terminal_catd X) R YY1;


/*****************************************
* # FIBRATIONS: CARTESIAN TRANSPORT
******************************************/

constant symbol isFibration_con: Π [X : cat] (XX : catd X), TYPE;
constant symbol isFibration_cov: Π [X : cat] (XX : catd X), TYPE;

constant symbol Fibre_isFibration_con : Π [X I : cat] (A : catd X) (A_isf : isFibration_con A) (x : func I X),
isFibration_con (Fibre_catd A x);
constant symbol Fibre_isFibration_cov : Π [X I : cat] (A : catd X) (A_isf : isFibration_cov A) (x : func I X),
 isFibration_cov (Fibre_catd A x);

symbol Fibration_con_funcd : Π [I X X'  : cat] [x'x : func X' X] [G : func X I] [JJ : catd X'] [F : func X' I] [II : catd I] (II_isf : isFibration_con II),
Π (FF : funcd JJ F II) (f : hom x'x (Unit_mod G Id_func) F), 
funcd JJ x'x (Fibre_catd II G); // aka f*FF

symbol Fibration_cov_funcd : Π [I X X'  : cat] [x'x : func X' X] [G : func X I] 
[JJ : catd X'] [F : func X' I] [II : catd I] /* II coCart */
(FF : funcd JJ F II) (f : hom F (Unit_mod Id_func G) x'x ), 
funcd JJ x'x  (Fibre_catd II G); // aka f!FF

constant symbol Fibration_con_elim_homd :  Π [I X X'  : cat] [x'x : func X' X] [G : func X I] 
 [JJ : catd X'] [F : func X' I] [II : catd I] (II_isf : isFibration_con II)
 (FF : funcd JJ F II) (f : hom x'x (Unit_mod G Id_func) F),
  homd f (Fibration_con_funcd II_isf FF f) (Unit_modd (Fibre_elim_funcd II G)  Id_funcd) FF;
 
constant symbol Fibration_con_intro_homd : Π [I X X'  : cat] [x'x : func X' X] [G : func X I] [JJ : catd X'] [F : func X' I] [II : catd I] (II_isf : isFibration_con II)
 (FF : funcd JJ F II) (f : hom x'x (Unit_mod G Id_func) F) 
 [X'0 : cat] [x'0x : func X'0 X] [X'' : cat] [x''x' : func X'' X'] [x''x'0 : func X'' X'0] 
 (x'0x' :  hom x''x'0 (Unit_mod x'0x x'x) x''x') [KK : catd X'0] (GG : funcd KK x'0x (Fibre_catd II G)) [HH : funcd (Fibre_catd JJ x''x') x''x'0 KK],
homd ((x'0x' '∘ ((x'0x)_'∘> f))) HH (Unit_modd (GG ∘>d (Fibre_elim_funcd II G)) Id_funcd) ((Fibre_elim_funcd JJ (x''x')) ∘>d FF) → 
homd x'0x' HH (Unit_modd GG (Fibration_con_funcd II_isf FF f)) (Fibre_elim_funcd JJ (x''x'));


// naturality
rule @∘>d _ _ _ _ _ _ $Z _ $ZZ  (Fibration_con_funcd $II_isf $FF $f) ↪ (Fibration_con_funcd $II_isf ($ZZ ∘>d $FF) ($f ∘↓ $Z)) ;
rule (Fibration_con_intro_homd $II_isf $FF $f  $x'0x' $GG $ii) ∘↓d (Fibre_elim_funcd _ $zz) 
 ↪ (Fibration_con_intro_homd $II_isf $FF  $f  ($x'0x' ∘↓ $zz) $GG ($ii ∘↓d (Fibre_elim_funcd _ $zz))) ;

// rule (@∘↓d _ _ _ _ _ _ _ _ _ _ _ _ _ (Fibration_con_intro_homd $G $FF $f $x'0x $x'0x' $GG $ii) _ $z _ $zz) 
// ↪ (Fibration_con_intro_homd $G $FF  $f $x'0x ($x'0x' ∘↓ $z) $GG ($ii ∘↓d $zz)) ;

// ??TODO outer naturality of fibred yoneda: Fibration_con_intro_homd''' applied to Fibration_con_intro_homd''' (xyz ∘> $f) to relate Fibration_con_funcd''' (xyz ∘> $f)  to Fibration_con_funcd''' $f
// so that so that composing with it is the corresponding action, which is then obviously natural (that is, the component-wise-specified output transf as univhoms is then natural)

// universality/deformation
rule (Fibration_con_intro_homd $II_isf $FF $f  $x'0x' $GG $ii) '∘d (($GG)_'∘>d (Fibration_con_elim_homd $II_isf $FF $f)) ↪ $ii;

//TODO: normality, lift id to id


/*****************************************
* # FIBRATIONS: COMMA CATEGORY
******************************************/

constant symbol Comma_con_catd : Π [A B : cat] (R : mod A B) (BB : catd B) , catd A;
constant symbol Comma_cov_catd : Π [A B : cat] (AA : catd A) (R : mod A B), catd B;

constant symbol Comma_con_intro_funcd : Π [A B I : cat] [R : mod A B] (BB : catd B) [x : func I A] [y : func I B] (r : hom x R y),
funcd (Fibre_catd BB y) x (Comma_con_catd R BB);
constant symbol Comma_cov_intro_funcd : Π [A B I : cat] (AA : catd A) [R : mod A B] [x : func I A] [y : func I B] (r : hom x R y),
funcd (Fibre_catd AA x) y (Comma_cov_catd AA R);
 
rule Fibre_catd (Comma_con_catd $R $BB) $F ↪ (Comma_con_catd ($F ∘>> $R) $BB)
with Fibre_catd (Comma_cov_catd $AA $R) $G ↪ (Comma_cov_catd $AA ($R <<∘ $G)) ;

rule (Fibre_elim_funcd /*(Fibre_catd $BB $y)*/ _ $zz) ∘>d (@Comma_con_intro_funcd _ _ _ _ $BB _ $y $r) 
↪ (Comma_con_intro_funcd $BB ($r ∘↓ $zz));
rule (Fibre_elim_funcd /*(Fibre_catd $AA $x)*/ _ $zz) ∘>d (@Comma_cov_intro_funcd _ _ _ $AA _  $x _ $r) 
↪ (Comma_cov_intro_funcd $AA ($r ∘↓ $zz));

//TODO: REVIEW AND ERASE THIS? FOR THE SIMPLER VERSION? Comma_con_homd_v2
constant symbol Comma_con_comp_funcd : Π [A B I : cat] (R : mod A B) (BB : catd B) (F : func I A),
funcd (Comma_con_catd (F ∘>> R) BB) F (Comma_con_catd R BB);
constant symbol Comma_cov_comp_funcd : Π [A B I : cat] (AA : catd A) (R : mod A B) (G : func I B),
funcd (Comma_cov_catd AA (R <<∘ G )) G (Comma_cov_catd AA R);
rule (Comma_con_comp_funcd _ _ $F') ∘>d (Comma_con_comp_funcd $R $BB $F)
↪ (Comma_con_comp_funcd $R $BB ($F' ∘> $F));

constant symbol Comma_con_homd : Π [A B I : cat] [R : mod A B] (BB : catd B) [x : func I A] [y : func I B] (r : hom x R y),
Π [J] [x' : func J I] [J0] [F : func J0 A] [x'x : func J J0] (x'x_ : hom x'x (Unit_mod F x) x') , 
homd ( x'x_ ) (Comma_con_intro_funcd BB ( x'x_ '∘  ((F)_'∘> r) )) (Unit_modd (Comma_con_comp_funcd R BB F) (Comma_con_intro_funcd BB r)) (Fibre_elim_funcd (Fibre_catd BB y) x');

//REVIEW: use this simpler instead?
constant symbol Comma_con_homd_v2 : Π [A B I : cat] [R : mod A B] (BB : catd B) [x : func I A] [y : func I B] (r : hom x R y),
Π [J] [x' : func J I]   [x'x : func J A] (x'x_ : hom x'x (Unit_mod Id_func x) x') , 
homd ( x'x_ ) (Comma_con_intro_funcd BB ( x'x_ '∘  ((Id_func)_'∘> r) )) (Unit_modd Id_funcd (Comma_con_intro_funcd BB r)) (Fibre_elim_funcd (Fibre_catd BB y) x');

constant symbol Comma_cov_intro_homd : Π [A B I : cat] (AA : catd A) [R : mod A B] [x : func I A] [y : func I B] (r : hom x R y),
Π [K] [y' : func K I] [y'y : func K B] (y'y_ : hom y' (Unit_mod y Id_func) y'y) ,
homd ( y'y_ ) (Fibre_elim_funcd (Fibre_catd AA x) y') (Unit_modd (Comma_cov_intro_funcd AA r) Id_funcd) (Comma_cov_intro_funcd AA ( (r ∘>'_(_)) ∘' y'y_ ));

//TODO: composition of hom

type λ [A B I : cat] [R : mod A B] (BB : catd B) [x : func I A] [y : func I B] (r : hom x R y)
 [J] [x' : func J I] [J0] [F : func J0 A] [x'x] (x'x_ : hom x'x (Unit_mod F x) x')
 [J'] [x'' : func J' J] [J0'] [F' : func J0' J0] [x''x'] (x''x'_ : hom x''x' (Unit_mod F' x'x) x''),
  (((Comma_con_homd BB (x'x_ '∘  ((F)_'∘> r)) x''x'_) ) '∘d  (( _ ) _'∘>d  (Comma_con_homd BB r x'x_))) ;
//Π A: cat, Π B: cat, Π I: cat, Π R: mod A B, Π BB: catd B, Π x: func I A, Π y: func I B, Π r: hom x R y, Π J: cat, Π x': func J I, Π J0: cat, Π F: func J0 A, Π x'x: func J J0, Π x'x_: hom x'x (Unit_mod F x) x', Π J': cat, Π x'': func J' J, Π J0': cat, Π F': func J0' J0, Π x''x': func J' J0', Π x''x'_: hom x''x' (Unit_mod F' x'x) x'', homd (x''x'_ '∘ (F' _'∘> x'x_)) (Comma_con_intro_funcd BB (x''x'_ '∘ (F' _'∘> (x'x_ '∘ (F _'∘> r))))) (Comma_con_comp_funcd (F ∘>> R) BB F' ∘>>d Unit_modd (Comma_con_comp_funcd R BB F) (Comma_con_intro_funcd BB r)) (Fibre_elim_funcd (Fibre_catd BB (y <∘ x')) x'' ∘>d Fibre_elim_funcd (Fibre_catd BB y) x')

type λ [A B I : cat] [R : mod A B] (BB : catd B) [x : func I A] [y : func I B] (r : hom x R y)
 [J] [x' : func J I] [J0] [F : func J0 A] [x'x] (x'x_ : hom x'x (Unit_mod F x) x')
 [J'] [x'' : func J' J] [J0'] [F' : func J0' J0] [x''x'] (x''x'_ : hom x''x' (Unit_mod F' x'x) x''),
 ((Comma_con_homd BB r (x''x'_ '∘  ((F')_'∘> x'x_ ))) ) ;
//Π A: cat, Π B: cat, Π I: cat, Π R: mod A B, Π BB: catd B, Π x: func I A, Π y: func I B, Π r: hom x R y, Π J: cat, Π x': func J I, Π J0: cat, Π F: func J0 A, Π x'x: func J J0, Π x'x_: hom x'x (Unit_mod F x) x', Π J': cat, Π x'': func J' J, Π J0': cat, Π F': func J0' J0, Π x''x': func J' J0', Π x''x'_: hom x''x' (Unit_mod F' x'x) x'', homd (x''x'_ '∘ (F' _'∘> x'x_)) (Comma_con_intro_funcd BB ((x''x'_ '∘ (F' _'∘> x'x_)) '∘ ((F' ∘> F) _'∘> r))) (Unit_modd (Comma_con_comp_funcd R BB (F' ∘> F)) (Comma_con_intro_funcd BB r)) (Fibre_elim_funcd (Fibre_catd BB y) (x' <∘ x''))

//Cannot solve x''x'_ '∘ (F' _'∘> (x'x_ '∘ (F _'∘> r))) ≡ (x''x'_ '∘ (F' _'∘> x'x_)) '∘ ((F' ∘> F) _'∘> r).

//PROBLEM REVIEW  
type λ [A B I : cat] [R : mod A B] (BB : catd B) [x : func I A] [y : func I B] (r : hom x R y)
 [J] [x' : func J I] [J0] [F : func J0 A] [x'x] (x'x_ : hom x'x (Unit_mod F x) x')
 [J'] [x'' : func J' J] [J0'] [F' : func J0' J0] [x''x'] (x''x'_ : hom x''x' (Unit_mod F' x'x) x''),
  (((Comma_con_homd BB (x'x_ '∘  ((F)_'∘> r)) x''x'_) ) '∘d  (( _ ) _'∘>d  (Comma_con_homd BB r x'x_)))
       = ((Comma_con_homd BB r (x''x'_ '∘  ((F')_'∘> x'x_ ))) );


constant symbol Comma_con_elim_funcd : Π [I X : cat] (G : func X I) [II : catd I] (II_isf : isFibration_con II) [JJ : catd I] /* JJ is non cart */
(FF : funcd JJ Id_func II), //OK
funcd (Comma_con_catd (Unit_mod G Id_func) JJ) G II;
constant symbol Comma_cov_elim_funcd : Π [I X : cat] (G : func X I) [II : catd I] (II_isf : isFibration_cov II) [JJ : catd I] /* JJ is non cart */
(FF : funcd JJ Id_func II),
funcd (Comma_cov_catd  JJ (Unit_mod Id_func G)) G II;

constant symbol Comma_con_elim_homd : Π [I X X'  : cat] [x'x : func X' X] (G : func X I) //OK
[JJ : catd I] [F : func X' I] [II : catd I] (II_isf : isFibration_con II)
(FF : funcd JJ Id_func II) (f : hom x'x (Unit_mod G Id_func) F),
homd f (Comma_con_intro_funcd JJ f) (Unit_modd (Comma_con_elim_funcd G II_isf FF) Id_funcd) ((Fibre_elim_funcd JJ F) ∘>d FF);
constant symbol Comma_cov_elim_homd : Π [I X X'  : cat] [x'x : func X' X] (G : func X I) //OK
[JJ : catd I] [F : func X' I] [II : catd I] (II_isf : isFibration_cov II)
(FF : funcd JJ Id_func II) (f : hom F (Unit_mod Id_func G) x'x),
homd f ((Fibre_elim_funcd JJ F) ∘>d FF) (Unit_modd Id_funcd (Comma_cov_elim_funcd G II_isf FF)) (Comma_cov_intro_funcd JJ f);

rule (Comma_con_comp_funcd _ _ $H) ∘>d (Comma_con_elim_funcd $G $II_isf $FF) 
 ↪ (Comma_con_elim_funcd ($H ∘> $G) $II_isf $FF);


type λ [I X X'  : cat] [x'x : func X' X] (G : func X I) //OK
[JJ : catd I] [F : func X' I] [II : catd I] (II_isf : isFibration_con II)
(FF : funcd JJ Id_func II) (f : hom x'x (Unit_mod G Id_func) F)
[X'0] (x'0x : func X'0 X) [X''] [x''x' : func X'' X'] [x''x'0 : func X'' X'0] 
(x'0x' :  hom x''x'0 (Unit_mod x'0x x'x) x''x'), 

 ((Comma_con_homd JJ f x'0x' ) '∘d
 (( _ ) _'∘>d (Comma_con_elim_homd G II_isf FF f))) 
 = (Comma_con_elim_homd (x'0x ∘> G) II_isf FF (x'0x' '∘ ( (_ ) _'∘> f)));
// todo aso beta for cov

//TODO: REVIEW SLOW
//-NOPE-->-FAILS ONLY BECAUSE LACKING THIS WHICH IS SLOW , FAILS ALSO BECAUSE NO BETA RULE
// rule (@Fibration_con_funcd _ _ _ _ $x'x $G $FF ((Func_con_hom $G $x'0x ∘>'_ $F) ∘' $f) )
// ↪ (Fibration_con_funcd $G $FF $f ) ;
// rule (@Fibration_con_funcd _ _ _ _ ($x'x ∘> $x'0x)  $G $x'y $F $II $FF (@∘' _ _ _ _ _ (Unit_mod ($x'0x ∘> $G) $F) _ $x'x $x'y _ _ (Func_con_hom $G $x'0x ∘>'_ $F)  $f) )
// ↪ (@Fibration_con_funcd _ _ _ _ $x'x ($x'0x ∘> $G) $x'y $F $II $FF $f ) ;

rule (Comma_con_intro_funcd $JJ $f) ∘>d (Comma_con_elim_funcd $G $II_isf $FF)
↪ (Fibration_con_funcd $II_isf ((Fibre_elim_funcd $JJ _) ∘>d $FF) $f) ∘>d (Fibre_elim_funcd _ $G) ;

assert [I X : cat] [G : func X I] [II : catd I] (II_isf : isFibration_con II) [JJ : catd I] (FF : funcd JJ Id_func II)
 [J : cat] [x: func J X] [F : func J I] (f : hom x (Unit_mod G Id_func) F) ⊢
(Comma_con_intro_funcd JJ f) ∘>d (Comma_con_elim_funcd G II_isf FF)
≡ (Fibration_con_funcd II_isf ((Fibre_elim_funcd JJ F) ∘>d FF) f) ∘>d (Fibre_elim_funcd II G);
// : funcd (Fibre_catd JJ F) (x ∘> G) II

//NOTE this says that the universal comparaison morphism for the algebraic Comma_con_elim_homd,
// which would use some absent universal intro rule similar as Fibration_con_intro_homd, is still definable
type λ [I X X'  : cat] [x'x : func X' X] (G : func X I) //OK
[JJ : catd I] [F : func X' I] [II : catd I] (II_isf : isFibration_con II)
(FF : funcd JJ Id_func II) (f : hom x'x (Unit_mod G Id_func) F)
[X'0] [x'0x : func X'0 X] [X''] [x''x' : func X'' X'] [x''x'0 : func X'' X'0] 
(x'0x' :  hom x''x'0 (Unit_mod x'0x x'x) x''x'), 
((Comma_con_homd JJ f x'0x' ) '∘d
((_) _'∘>d (Func_con_homd (Comma_con_elim_funcd G II_isf FF) (Comma_con_intro_funcd JJ f)))) 
=  ((Fibration_con_intro_homd II_isf ((Fibre_elim_funcd JJ F) ∘>d FF) f x'0x' (Fibre_intro_funcd _ G x'0x (Comma_con_elim_funcd (x'0x ∘> G) II_isf FF))
                  (Comma_con_elim_homd (x'0x ∘> G) II_isf FF (x'0x' '∘ (x'0x _'∘> f))))
     '∘d (( _ ) _'∘>d 
               (Func_con_homd (Fibre_elim_funcd II G) (Fibration_con_funcd II_isf ((Fibre_elim_funcd JJ F) ∘>d FF) f))));


//rewrite rule to make concrete how is the derived transport for the pullback of fibration,
// definable from the transport for the original fibration
symbol Pullback_Fibration_con_funcd [I X X'  : cat] [x'x : func X' X] [G : func X I] 
[JJ : catd X'] [F : func X' I] [I0] (i0 : func I I0) (II0 : catd I0) (II0_isf : isFibration_con II0)
(FF : funcd JJ F (Fibre_catd II0 i0)) (f : hom x'x (Unit_mod G Id_func) F):
funcd JJ x'x  (Fibre_catd (Fibre_catd II0 i0) G)
≔ Fibration_con_funcd II0_isf (FF ∘>d (Fibre_elim_funcd II0 i0))
      (f '∘ ( ( G ) _'∘> (Func_con_hom i0 Id_func) ) );

rule @Fibration_con_funcd _ _ _ _ $G _ _ (Fibre_catd $II0 $i0) (Fibre_isFibration_con $II0 $II0_isf $i0) $FF $f
 ↪ Pullback_Fibration_con_funcd $i0 $II0 $II0_isf $FF $f;


/*****************************************
* # FIBRATIONS: EXAMPLE OF FIBRED PRODUNCTOR, SQUARES FIBRED BY THEIR DIAGONAL
******************************************/

//example of fibred profunctor: squares fibred by their diagonal
constant symbol Comma_modd : Π [A B : cat] (AA : catd A) (R : mod A B) (BB : catd B),
  modd (Comma_con_catd R BB) R (Comma_cov_catd AA R);

//TODO: REVIEW NOPE, too general ?
//  .constant symbol Comma_homd : Π [A B I : cat] (AA : catd A) [R : mod A B] (BB : catd B) 
// [x : func I A] [y : func I B],
// Π [J0] [F : func J0 A] [x'x : func I J0] (x'x_ : hom x'x (Unit_mod F x) Id_func) , 
// Π [J1] [G : func J1 B] [y'y : func I J1] (y'y_ : hom Id_func (Unit_mod y G) y'y) ,
// Π (s : hom x'x (F ∘>> R) y) (t : hom x (R <<∘ G) y'y) (r : hom x'x (F ∘>> (R <<∘ G)) y'y), 
// homd r (Comma_con_intro_funcd BB s) 
// ((Comma_con_comp_funcd R BB F) ∘>>d ((Comma_modd AA R BB) d<<∘ (Comma_cov_comp_funcd AA R G))) 
//  (Comma_cov_intro_funcd AA t); //redo

 //example of fibred profunctor: squares fibred by their diagonal
constant symbol Comma_homd : Π [A B I : cat] (R : mod A B) [x : func I A] [y : func I B],
Π [J0] [F : func J0 A] [x' : func I J0] (x'x : hom x' (Unit_mod F x) Id_func), 
Π [J1] [G : func J1 B] [y' : func I J1] (yy' : hom Id_func (Unit_mod y G) y'),
Π (s : hom x' (F ∘>> R) y) (t : hom x (R <<∘ G) y') (r : hom x' (F ∘>> (R <<∘ G)) y'), 
τ (( x'x '∘  ((F)_'∘> t) ) = r) → τ (( (s ∘>'_(G)) ∘' yy' ) = r) → 
homd r (Comma_con_intro_funcd (Terminal_catd B) s) 
 ((Comma_con_comp_funcd R (Terminal_catd B) F) ∘>>d ((Comma_modd (Terminal_catd A) R (Terminal_catd B)) d<<∘ (Comma_cov_comp_funcd (Terminal_catd A) R G)))
 (Comma_cov_intro_funcd (Terminal_catd A) t);

opaque symbol Comma_homd'_lemma1 : Π [A B I : cat] [R : mod A B] [x : func I A] [y : func I B],
Π [J0] [F : func J0 A] [x' : func I J0] (x'x : hom x' (Unit_mod F x) Id_func) , 
Π (t : hom x R y) (r : hom x' (F ∘>> R) y), 
Π [K0] [F' : func K0 J0] [x'' : func I K0] (x''x' : hom x'' (Unit_mod F' x') Id_func) , 
τ (( x'x '∘  ((F)_'∘> t) ) = r) → τ (( ( x''x' '∘ ( (F')_'∘> x'x) ) '∘  ((_)_'∘> t) ) = (x''x' '∘ ((F')_'∘> r))) ≔
begin 
  assume _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; assume prf;
  rewrite left prf; reflexivity;
end;

opaque symbol Comma_homd'_lemma2 : Π [A B I : cat] [R : mod A B] [x : func I A] [y : func I B],
Π [J1] [G : func J1 B] [y' : func I J1] (yy' : hom Id_func (Unit_mod y G) y') ,
Π (s : hom x R y) (r : hom x (R <<∘ G) y'), 
Π [K0] [F' : func K0 A] [x'' : func I K0] (x''x' : hom x'' (Unit_mod F' x) Id_func) , 
τ (( (s ∘>'_(G)) ∘' yy' ) = r) → 
τ (( (( x''x' '∘ ( (F')_'∘> s) ) ∘>'_(G)) ∘' yy' ) =  (x''x' '∘ ((F')_'∘> r))) ≔
begin 
  assume A B I R x y J1 G y' yy' s r K0 F' x'' x''x'; assume prf;
  rewrite left prf; apply (associativity_con_metatheorem yy' s x''x');
end;

symbol todo_rule_Comma_homd'_Comma_con_homd' ≔ λ [A B I : cat]  (R : mod A B)  [x : func I A] [y : func I B],
λ   [J0] [F : func J0 A] [x' : func I J0] (x'x : hom x' (Unit_mod F x) Id_func) , 
λ   [J1] [G : func J1 B] [y' : func I J1] (yy' : hom Id_func (Unit_mod y G) y') ,
λ  (s : hom x' (F ∘>> R) y) (t : hom x (R <<∘ G) y') (r : hom x' (F ∘>> (R <<∘ G)) y'), 
λ   [K0] [F' : func K0 J0] [x'' : func I K0] (x''x' : hom x'' (Unit_mod F' x') Id_func) , 
λ (prf : τ (( x'x '∘  ((F)_'∘> t) ) = r) ) (prf2 : τ (( (s ∘>'_(G)) ∘' yy' ) = r)),
 (Comma_con_homd (Terminal_catd B) s x''x' )  '∘d 
   (( _ ) _'∘>d (Comma_homd R x'x yy' s t r ) prf prf2)
= (Comma_homd R ( x''x' '∘ ( (F')_'∘> x'x) ) yy' (x''x' '∘ ((F')_'∘> s)) t (x''x' '∘ ((F')_'∘> r)) 
     (Comma_homd'_lemma1 x'x t r x''x' prf) 
     (Comma_homd'_lemma2 yy' s  r x''x' prf2) );


/*****************************************
* # CATEGORY OF ELEMENTS AS AN INSTANCE OF THE COMMA FIBRATION CATEGORY
******************************************/

injective symbol Elements_cat: Π [B : cat] (R : mod Terminal_cat B), cat;
rule @Elements_cat $B $R ↪ Context_cat (Comma_cov_catd (Terminal_catd _) $R);

injective symbol Elements_proj_func : Π [B : cat] (R : mod Terminal_cat B), func (Elements_cat R) B;
rule @Elements_proj_func $B $R ↪ Context_elimCat_func (Comma_cov_catd (Terminal_catd _) $R);

//todo : relax (Terminal_func I) to any x ?
injective symbol Elements_intro_func : Π [B I : cat] [R : mod Terminal_cat B] [y : func I B] (r : hom (Terminal_func I) R y),
func I (Elements_cat R);
rule @Elements_intro_func $B $I $R $y $r ↪ Context_intro_func (Comma_cov_intro_funcd (Terminal_catd _) $r);

assert [B I : cat] [R : mod Terminal_cat B] [y : func I B] (r : hom (Terminal_func I) R y) ⊢
@Elements_intro_func B I R y r ∘> Elements_proj_func R ≡ y;
// rule (@Elements_intro_func _ _ _ $y $r ∘> Elements_proj_func _) ↪ $y;

assert [B I : cat] [R : mod Terminal_cat B] [y : func I B] (r : hom (Terminal_func I) R y) [J] (F : func J I) ⊢
F ∘> @Elements_intro_func B I R y r ≡ (@Elements_intro_func _ _ _ (F ∘> y) (r ∘↓ F));
// rule $F ∘> (@Elements_intro_func _ _ _ $y $r) ↪ (@Elements_intro_func _ _ _ ($F ∘> $y) ($r ∘↓ $F));

injective symbol Elements_intro_hom : Π [B I : cat] [R : mod Terminal_cat B] [y : func I B] (r : hom (Terminal_func I) R y),
Π [K] [y' : func K I] [y'y : func K B] (y'y_ : hom y' (Unit_mod y Id_func) y'y) ,
hom y' (Unit_mod (Elements_intro_func r) Id_func) (Elements_intro_func( (r ∘>'_(Id_func)) ∘' y'y_ ));
rule Elements_intro_hom $r $y'y_ ↪ Context_intro_hom $y'y_ (Comma_cov_intro_homd (Terminal_catd _) $r $y'y_);

assert [B I : cat] [R : mod Terminal_cat B] [y : func I B] (r : hom (Terminal_func I) R y) [K] [y' : func K I] [y'y : func K B] (y'y_ : hom y' (Unit_mod y Id_func) y'y) ⊢
(Elements_intro_hom r y'y_) '∘ (Context_elimMod_transf (Unit_modd _ Id_funcd) ) ≡ y'y_;
assert [B I : cat] [R : mod Terminal_cat B] [y : func I B] (r : hom (Terminal_func I) R y) [K] [y' : func K I] [y'y : func K B] (y'y_ : hom y' (Unit_mod y Id_func) y'y) ⊢
(Elements_intro_hom r y'y_) '∘ (_)_'∘> (Func_con_hom (Elements_proj_func _) _) ≡ y'y_;


/*****************************************
* # UNIVERSE AND UNIVERSAL FIBRATION
******************************************/

constant symbol Universe_con_cat : cat;
constant symbol Universe_cov_cat : cat;
constant symbol Universe_con_catd : catd Universe_con_cat;
constant symbol Universe_cov_catd : catd Universe_cov_cat;
constant symbol Universe_con_isFibration_con : isFibration_con Universe_con_catd;
constant symbol Universe_cov_isFibration_cov : isFibration_cov Universe_cov_catd;

 //SIGNIFICANT: note no use of explicit Op_cat contravariance or of extra notion of contravariant functor, 
// here the contravariance is intrinsic baked into the contravariant universe, 
// and each independent development of the two universes need not interact via Op_ ,
// better: each don't even need the existance of Op_
symbol Universe_con_func : Π [X : cat] (A : catd X) (A_isf : isFibration_con A), func  X Universe_con_cat;
symbol Universe_cov_func : Π [X : cat] (A : catd X) (A_isf : isFibration_cov A), func X Universe_cov_cat;

symbol Universe_con_funcd : Π [X : cat] (A : catd X) (A_isf : isFibration_con A), funcd A (Universe_con_func A A_isf) Universe_con_catd;
symbol Universe_cov_funcd : Π [X : cat] (A : catd X) (A_isf : isFibration_cov A), funcd A (Universe_cov_func A A_isf) Universe_cov_catd;
 
rule $F ∘> (Universe_con_func $A $A_isf) ↪ (Universe_con_func (Fibre_catd $A $F) (Fibre_isFibration_con $A $A_isf $F));
rule (Fibre_elim_funcd $A $F) ∘>d (Universe_con_funcd $A $A_isf) ↪ (Universe_con_funcd (Fibre_catd $A $F) (Fibre_isFibration_con $A $A_isf $F));

rule (Universe_con_func (Fibre_catd Universe_con_catd $F) (Fibre_isFibration_con Universe_con_catd Universe_con_isFibration_con $F)) ↪ $F;
rule (Universe_con_funcd (Fibre_catd Universe_con_catd $F) (Fibre_isFibration_con Universe_con_catd Universe_con_isFibration_con $F)) ↪ Fibre_elim_funcd Universe_con_catd $F;

//strict universe, optional? or use Fibre_intro isEquiv instead of declaring it identity 
rule (Fibre_catd Universe_con_catd (Universe_con_func $A _)) ↪ $A;
rule (Fibre_elim_funcd Universe_con_catd (Universe_con_func $A $A_isf)) ↪ (Universe_con_funcd $A $A_isf);

//note: these below are copy-paste replace _con_ by _cov_
rule $F ∘> (Universe_cov_func $A $A_isf) ↪ (Universe_cov_func (Fibre_catd $A $F) (Fibre_isFibration_cov $A $A_isf $F));
rule (Fibre_elim_funcd $A $F) ∘>d (Universe_cov_funcd $A $A_isf) ↪ (Universe_cov_funcd (Fibre_catd $A $F) (Fibre_isFibration_cov $A $A_isf $F));

rule (Universe_cov_func (Fibre_catd Universe_cov_catd $F) (Fibre_isFibration_cov Universe_cov_catd Universe_cov_isFibration_cov $F)) ↪ $F;
rule (Universe_cov_funcd (Fibre_catd Universe_cov_catd $F) (Fibre_isFibration_cov Universe_cov_catd Universe_cov_isFibration_cov $F)) ↪ Fibre_elim_funcd Universe_cov_catd $F;

//strict universe, optional? or use Fibre_intro isEquiv instead of declaring it identity 
rule (Fibre_catd Universe_cov_catd (Universe_cov_func $A _)) ↪ $A;
rule (Fibre_elim_funcd Universe_cov_catd (Universe_cov_func $A $A_isf)) ↪ (Universe_cov_funcd $A $A_isf);

// grammatical (univalent) universe by declaring an inverse to the transport for the universe fibration
injective symbol Universe_Fibration_con_funcd_inv : Π [X Y: cat] (F : func X Universe_con_cat) (G : func Y Universe_con_cat) 
[xy : func X Y], funcd (Fibre_catd Universe_con_catd F) xy (Fibre_catd Universe_con_catd G) 
→ hom xy (Unit_mod G Id_func) F;

injective symbol Universe_Fibration_cov_funcd_inv : Π [X Y: cat] (F : func X Universe_cov_cat) (G : func Y Universe_cov_cat) 
[xy : func X Y], funcd (Fibre_catd Universe_cov_catd F) xy (Fibre_catd Universe_cov_catd G) 
→ hom F (Unit_mod Id_func G) xy;

injective symbol Universe_Fibration_con_funcd  [X Y: cat] [F : func X Universe_con_cat] [G : func Y Universe_con_cat] 
[xy : func X Y] (h : hom xy (Unit_mod G Id_func) F) :
funcd (Fibre_catd Universe_con_catd F) xy (Fibre_catd Universe_con_catd G) ≔ 
 Fibration_con_funcd Universe_con_isFibration_con (Fibre_elim_funcd Universe_con_catd F) h;

rule Fibration_con_funcd Universe_con_isFibration_con (Fibre_elim_funcd Universe_con_catd $F) (Universe_Fibration_con_funcd_inv $F $G $HH) ↪ $HH;
rule (Universe_Fibration_con_funcd_inv $F $G (@Fibration_con_funcd _ _ _ _ $G _ _ _ Universe_con_isFibration_con (Fibre_elim_funcd Universe_con_catd $F) $h)) ↪ $h;


/*****************************************
* # TENSOR (AND KAN EXTENSIONS AND CO-YONEDA REDUCTIONS) HOM FOR MODULES (PROFUNCTORS)
******************************************/


//REVIEW: ?TODO ALLOW OVER SPAN OF FUNC, SIMILAR AS FOR PULLBACK-PRODUCT OF FIBRATIONS
injective symbol ⊗ : Π [A B X : cat], mod A B → mod B X → mod A X; //Tensor_mod;
notation ⊗ infix left 70;

rule ($R ⊗ $S) <<∘ $G ↪ $R ⊗ ($S <<∘ $G);
rule $G ∘>> ($R ⊗ $S) ↪ ($G ∘>> $R) ⊗ $S;

//  constant symbol Tensor_cov_transf : Π [A' I X' A X: cat] [P' : mod A' I] [Q' : mod I X'] 
//  [P : mod A I] [Q : mod I X] [F : func A' A] [G : func X' X],
//  transf P' F P Id_func → transf Q' Id_func Q G →
//  transf (P' ⊗ Q') F (P ⊗ Q) G;
constant symbol Tensor_cov_transf : Π [A' I I' X' A X: cat] [P' : mod A' I'] [Q' : mod I' X'] 
[P : mod A I] [Q : mod I X] [F : func A' A] [G : func X' X] , Π (M : func I' I),
transf P' F (P <<∘ M) Id_func → transf Q' M Q G → // usual asymmetry for composable pair
transf (P' ⊗ Q') F (P ⊗ Q) G;

constant symbol Tensor_con_transf : Π [A' I I' X' A X: cat] [P' : mod A' I'] [Q' : mod I' X'] 
[P : mod A I] [Q : mod I X] [F : func A' A] [G : func X' X] , Π (M : func I' I),
transf P' F P M → transf Q' Id_func (M ∘>> Q) G → // usual asymmetry for composable pair
transf (P' ⊗ Q') F (P ⊗ Q) G;

rule (Tensor_cov_transf $M $t $s) <<∘1 $H ↪ (Tensor_cov_transf $M $t ($s <<∘1 $H))
with $H 1∘>> (Tensor_cov_transf $M $t $s) ↪ (Tensor_cov_transf $M ($H 1∘>> $t) $s);

//rule Op_transf (Tensor_cov_transf $rr $ss) ↪ (Tensor_cov_transf (Op_transf $ss) (Op_transf $rr));
// rule Op_transf (Tensor_cov_transf $M $rr $ss) ↪ (Tensor_cov_transf (Op_func $M) (Op_transf $ss) (Op_transf $rr));

constant symbol Tensor_con_hom_hom  : Π [A X B I : cat] [P : mod A B] [Q : mod B X]
[F : func I A] [G : func I X], Π (M : func I B),
hom F P M → hom Id_func (M ∘>> Q) G → hom F (P ⊗ Q) G;

constant symbol Tensor_cov_hom_hom  : Π [A X B I : cat] [P : mod A B] [Q : mod B X]
[F : func I A] [G : func I X] /* G ≔ Id_func */, Π (M : func I B),
hom F (P <<∘ M) Id_func → hom M Q G → hom F (P ⊗ Q) G;

constant symbol Tensor_cov_elim_transf : Π [A B A' J : cat] /* J ≔ Terminal_cat */ [F : func A A'] (P : mod A B) [Q : mod B J] /* Q ≔ Unit Id N */ [R : mod A' J],
/* no (further) naturality lacked (or even expressable) */
(Π [M : func J B], hom M Q Id_func → transf (P <<∘ M) F R Id_func) → 
transf (P ⊗ Q) F R Id_func;

rule (Tensor_cov_elim_transf $P $t_) ∘' (@Tensor_cov_hom_hom _ _ _ _ _ _ _ Id_func $M $p $q ) 
↪ (($t_ $M $q) ∘' $p);

constant symbol Tensor_cov_hom_transf : Π [A' B A X J : cat] [P' : mod A' J] 
[P : mod A B] [Q : mod B X] [F : func A' A] [G : func J X], Π (M : func J B),
transf P' F (P <<∘ M) Id_func → hom M Q G →
transf P' F (P ⊗ Q) G;

/* -----
* ## TENSOR AND COYONEDA REDUCTION */

//TODO: REVIEW:  is coyoneda reduction an instance of elim Tensor_elim ? would require some hom M (Unit Id N) i → transf (P <<∘ M) Id (P <<∘ N) i
//TODO: Could add rule (P ⊗ (Unit_mod Id_func Id_func)) ↪ P 
// or (P ⊗ (Unit_mod Id_func N)) ↪ P <<∘ N with rule coyoneda_Unit_Tensor_cov_transf t_ ↪ t_ (or its pullback <<∘1)
//TODO:  should at least set G to Id_func (also N to Id_func)
injective symbol coyoneda_Unit_Tensor_cov_transf : Π [A B A' B' : cat] [P : mod A B] [P' : mod A' B'] [F : func A A'] [G : func B B'] ,
transf P F P' G /* G ≔ Id_func */ → Π [J : cat] (N : func J B'), /* N possible via pullback*/
transf (P ⊗ (Unit_mod G N)) F (P' <<∘ N) Id_func; //transf (P ⊗ (Unit_mod Id_func Id_func)) F P' Id_func;

//REVIEW:
//DO NOT ERASE
// rule $P ⊗ (Unit_mod Id_func $N) 
// ↪ $P <<∘ $N;
// rule @coyoneda_Unit_Tensor_cov_transf _ _ _ _  _ _ _ Id_func  $t_ _ $N
// ↪ $t_ <<∘1 $N;

// evaluation of coyoneda at identity hom
rule (coyoneda_Unit_Tensor_cov_transf $pp _)  ∘'' (Tensor_cov_hom_transf Id_func $qq (Id_hom _))
 ↪ $pp ∘'' $qq;
rule (coyoneda_Unit_Tensor_cov_transf $pp _)  ∘' (Tensor_cov_hom_hom Id_func $p (Id_hom _))
↪ $pp ∘' $p;

rule (coyoneda_Unit_Tensor_cov_transf $pp _)  ∘'' (Tensor_cov_hom_transf Id_func $qq (Func_con_hom _ _))
 ↪ $pp ∘'' $qq; //not necessary but confluent
rule (coyoneda_Unit_Tensor_cov_transf $pp _)  ∘' (Tensor_cov_hom_hom Id_func $p (Func_con_hom Id_func Id_func))
↪ $pp ∘' $p; //not necessary but confluent


//  assert [A B A' : cat] [P : mod A B] [P' : mod A' B] [F : func A A'] 
//  (pp : transf P F P' Id_func )  A0 (Q: mod A0 B) H (qq : transf Q H P Id_func ) ⊢ eq_refl _ : τ(
// (coyoneda_Unit_Tensor_cov_transf pp Id_func)  ∘'' (Tensor_cov_hom_transf qq (Func_con_hom _ _))
//  =  pp ∘'' qq );

/* -----
* ## TODO: DEPENDENT TENSOR? */

constant symbol ⊗d : Π [A B X : cat] [AA : catd A][BB : catd B][XX : catd X]
  [R :mod A B] [S :mod B X], modd AA R BB → modd BB S XX →
  modd AA (R ⊗ S) XX;  //Tensor_modd;
 notation ⊗d infix left 70;


/*****************************************
* # INTERNAL HOM (IMPLICATION), LAMBDA CALCULUS FOR MODULES (PROFUNCTORS)
******************************************/

//Imply_cov_mod
constant symbol ⇐ : Π [A B X : cat], mod A B → mod X B → mod A X;
notation ⇐ infix left 60;

//Imply_con_mod
constant symbol ⇒ : Π [A B X : cat], mod A X → mod A B → mod X B;
notation ⇒ infix right 60;

rule ($R ⇐ $S) <<∘ $G ↪ $R ⇐ ($G ∘>> $S)
with ($R ⇒ $S) <<∘ $G ↪ $R ⇒ ($S <<∘ $G);

rule $G ∘>> ($R ⇒ $S) ↪ ($R <<∘ $G) ⇒ $S
with $G ∘>> ($R ⇐ $S) ↪ ($G ∘>> $R) ⇐ $S;

constant symbol Imply_cov_transf : Π [A B A' C  : cat] [O : mod A B] [O' : mod A' B]
[Q : mod C B] [C'] [M : func C' C] [Q' : mod C' B] [F : func A A']  , 
transf O F O' Id_func → transf Q' M Q Id_func → 
transf  ((O ⇐ Q) <<∘ M) //transf over span legs required here...? M outside, contravariance... nope ok
      F (O' ⇐ Q') Id_func;

constant symbol Imply_con_transf : Π [A B B' C  : cat] [O : mod A B] [O' : mod A B']
[Q : mod A C] [C'] [M : func C' C] [Q' : mod A C'] [G : func B B']  , 
transf O Id_func O' G → transf Q' Id_func Q M → 
transf  (M ∘>> (Q ⇒ O))
      Id_func (Q' ⇒ O') G;

constant symbol Imply_cov_hom_transf : Π [A B A' C  : cat] [O : mod A B] [O' : mod A' B]
  [Q' : mod C B] [F : func A A']   [L : func C B],
transf O F O' Id_func → hom Id_func Q' L → 
transf   (O ⇐ Q')
      F O' L;

 //todo eval-lambda with unit, so between hom and transf 
 //todo eval-lambda dependent over —/Γ context? or prefixed under Γ⊗— context?
injective symbol Eval_cov_transf : Π [A B  X A'  : cat] [P : mod A B] [Q : mod B X] 
 [O : mod A' X] [F : func A A'] ,
 transf P                       F (O ⇐ Q) Id_func →
 transf (P ⊗ Q)  F O                     Id_func;
 
//TODO ALLOW OVER SPAN OF FUNC, SIMILAR AS FOR DEPENDENT MORPHISM OF FIBRATIONS
// THEREFORE TENSOR ABSORB THE SPAN WHICH WOULD REPLACE Id_func AND SOLVES EARLIER PROBLEMS
injective symbol Lambda_cov_transf : Π [A B  X A' : cat] [P : mod A B] [Q : mod B X] 
 [O : mod A' X] [F : func A A'] ,
 transf (P ⊗ Q)  F O                     Id_func →
 transf P                       F (O ⇐ Q) Id_func;

injective symbol Eval_con_transf : Π [A B  X X'  : cat] [P : mod A B] [Q : mod B X] 
[O : mod A X'] [G : func X X'] ,
transf      Q                       Id_func (P ⇒ O) G →
transf (P ⊗ Q)                      Id_func      O  G;

//  rule (Eval_cov_transf $pq_o) ∘'' (Tensor_cov_transf $p'p $q'q)
// ↪ Eval_cov_transf ((Imply_cov_transf (Id_transf _) $q'q) ∘'' ($pq_o ∘'' $p'p));
// rule (Eval_cov_transf $pq_o) ∘'' (Tensor_cov_transf $M $p'p $q'q)
// ↪ Eval_cov_transf ((Imply_cov_transf (Id_transf _) $q'q) ∘'' (($pq_o <<∘1 $M) ∘'' $p'p));
rule (Eval_cov_transf $pq_o) ∘'' (Tensor_cov_transf $M $p'p $q'q)
↪ Eval_cov_transf ((Imply_cov_transf (Id_transf _) $q'q) ∘'' (($pq_o <<∘1 $M) ∘'' $p'p));

rule (Tensor_con_transf $M $p'p $q'q) ''∘ (Eval_con_transf $pq_o)
↪ Eval_con_transf ( ( $q'q ''∘ ($M 1∘>> $pq_o)) ''∘ (Imply_con_transf (Id_transf _) $p'p));

//eta
rule Lambda_cov_transf (Eval_cov_transf $t) ↪ $t;
//beta
rule (Eval_cov_transf (Lambda_cov_transf $t)) ↪ $t;

injective symbol Eval_cov_hom_transf : Π [A  X A' : cat] [Q : mod A X] 
[O : mod A' X] [F : func A A'] ,
hom                       F (O ⇐ Q) Id_func →
transf Q  F O                     Id_func;
 
injective symbol Lambda_cov_transf_hom : Π [A  X A'  : cat] [Q : mod A X] 
[O : mod A' X] [F : func A A'] ,
transf Q  F O                     Id_func  →
hom                       F (O ⇐ Q) Id_func;
 
rule Lambda_cov_transf_hom (Eval_cov_hom_transf $t) ↪ $t;
//beta
rule (Eval_cov_hom_transf (Lambda_cov_transf_hom $t)) ↪ $t;

//  assert [A B X A' X' : cat] [P : mod A B] [Q : mod B X] 
//  (O : mod A' X')  [F : func A A'] (L : func X X')
//  (pq_o : transf P                       F (⇐ O L Q) Id_func)
//  A0  X0 (M: func A0 A) (Z : func X0 X) 
//  (P': mod A0 B) (Q' : mod B X0) 
//  (p'p : transf P' M P Id_func) (q'q : transf Q' Id_func Q Z) ⊢ eq_refl _ : τ (
//  (Eval_cov_transf  pq_o)  ∘'' (Tensor_cov_transf p'p q'q)
//  = Eval_cov_transf  ((pq_o ∘'' p'p) ''∘ (Imply_cov_transf (Id_transf O) L q'q)) );

//TODO as rewrite rule
//  type λ [A X A' X' : cat] [Q : mod A X] 
//  (O : mod A' X')  [F : func A A'] (L : func X X')
//  (pq_o : hom                       F (⇐ O L Q) Id_func)
//   X0  (Z : func X0 X) 
//   (Q' : mod A X0) 
//   (q'q : transf Q' Id_func Q Z),
//  (Eval_cov_hom_transf  pq_o)  ∘'' q'q
// = Eval_cov_hom_transf  (pq_o '∘ (Imply_cov_transf (Id_transf O) L q'q));
 

symbol subst_Imply_cov_mod : 
Π [A B X : cat] [R : mod A B] [W : mod X B]
[I] (Z : func I B),
transf (R ⇐ W) Id_func ((R <<∘ Z) ⇐ (W <<∘ Z)) Id_func ≔
begin
  assume A B X R W I Z;
  refine (Lambda_cov_transf _);
  refine ( (Eval_cov_transf (Id_transf _)) <<∘1 Z);
end;

// covariant yoneda action by cone of arrows, including functor image of cone  (remember: covariant yoneda action = contravariant yoneda embedding...)
injective symbol comp_Imply_cov_mod : Π [I A B J : cat] [F : func I A] [R : mod A B] [G : func I B],
hom F R G → Π [K : cat] [N: func K B] [W : mod J K], 
transf ((Unit_mod G N) ⇐ W) F ((R <<∘ N) ⇐ W) Id_func  ≔
begin
assume I A B J F R G h K N W;
refine (Lambda_cov_transf _);
refine ( (h ∘>'_(N)) ∘'' (Eval_cov_transf (Id_transf _)) );
end;

/*****************************************
* # SETS, UNDERLYING GROUPOIDS, DISCRETE/GROUPOIDS AS CATEGORIES, UNIVALENT CATEGORIES
******************************************/

// (type_cat —) left adjoint to (func Terminal_cat —)
// REVIEW: inv rule is slow when this simbol is only injective
/* constant */ injective symbol type_cat : Type → cat;

rule type_cat unit_type ↪ Terminal_cat;

// adjunction:  triangular ► formulation , Dosen § 4.1.1. p.105
// left eta operation of adjunction
injective symbol type_intro_func : Π [I : Type] [A : cat], func (type_cat I) A → (τ I → func Terminal_cat A); /* _→_ is groupoidal functor for _=_ */

injective symbol type_map_func : Π [I J : Type], (τ I → τ J) → func (type_cat I) (type_cat J);

injective symbol type_elim_func : Π (A: cat), func (type_cat (func_type Terminal_cat A)) A;

rule type_map_func (type_intro_func $F) ∘> type_elim_func _ ↪ $F; //beta
rule type_intro_func (type_elim_func $A) $i ↪ $i; //eta // extensional form

//naturality
rule (type_intro_func $F $i) ∘> $G ↪ type_intro_func ($F ∘> $G) $i;
rule type_map_func $i_ ∘> type_map_func $j_ ↪ type_map_func (λ i, $j_ ($i_ i)) ;
rule type_map_func (λ i, i) ↪ Id_func; //second-order unif, ?bypass using symbols for function comp and id?

// inverse in type_cat are definitional //TODO: both cov and contra
injective symbol type_inv_hom: Π [A]  [J] [X Y : func J (type_cat A)],
hom Id_func (Unit_mod X Id_func) Y → hom Id_func (Unit_mod Y Id_func) X;

rule ((type_inv_hom $h) ∘>'_(_)) ∘' ($h) ↪ Func_con_hom _ _;
rule (type_inv_hom (type_inv_hom $h)) ↪ $h;
///REVIEW: SLOW 3 mins rule when in combinaison with non-constant injective type_cat, 
// OPTIONAL because it would be derivable (propositionally) from other 2 rules
// rule (($h) ∘>'_(_)) ∘' (@type_inv_hom _ $J $X $Y  $h) ↪ Func_con_hom $X Id_func;

// iso_cat also known as "core groupoid", definable from previous constructors
// could be generalized to: type_cat (func_type (type_cat J) A)  where global sections have shape J
injective symbol iso_cat (A : cat) : cat ≔ type_cat (func_type Terminal_cat /* (type_cat J) */ A);

// lift of hom, under the condition it has iso propositional property, which then becomes definitional //TODO: both cov and contra
constant symbol iso_intro_hom : Π [A: cat]  [X Y : func Terminal_cat A],
Π f : hom Id_func (Unit_mod X Id_func) Y, Π f' : hom Id_func (Unit_mod Y Id_func) X,
τ ((f ∘>'_(_)) ∘' f' = Func_con_hom X Id_func)
→ τ ((f' ∘>'_(_)) ∘' f = Func_con_hom Y Id_func)
→ hom Id_func (Unit_mod (type_intro_func Id_func X) Id_func) (type_intro_func Id_func Y);

rule (iso_intro_hom $f $f' _ _) '∘ (_) _'∘> Func_con_hom (type_elim_func $A) Id_func ↪ $f;
rule (type_inv_hom (iso_intro_hom $f $f' _ _)) '∘ (_) _'∘> Func_con_hom (type_elim_func $A) Id_func ↪ $f';

// generators for hom; any attempt to declare an eliminator (when the set is set of objects of some category),
// saying that these are the only arrows, is known as "univalence"
injective symbol type_intro_hom : Π [I : Type]  [X Y : τ I], // (I ≔ func_type Terminal_cat A)
τ (X = Y) → hom Id_func (Unit_mod (type_intro_func Id_func X) Id_func) (type_intro_func Id_func Y);

rule type_intro_hom (eq_refl _) ↪ Func_con_hom _ _;

// univalent category, axiomatically non-constructive
injective symbol univalent_iso_hom_eq : Π [A: cat] [X Y : func Terminal_cat A],
hom Id_func (Unit_mod (type_intro_func Id_func X) Id_func) (type_intro_func Id_func Y) → τ (X = Y);

rule type_intro_hom (univalent_iso_hom_eq $h) ↪ $h; //beta
rule univalent_iso_hom_eq (type_intro_hom $e) ↪ $e; //eta

/*****************************************
* # CONTAINER SETS, POLYNOMIAL MODULES, POLYNOMAIL FUNCTORS - PART 1. (cartierSolution15.lp FOR PART 2)
******************************************/

//---- LATER FILE cartierSolution15.lp HAS THE PART 2 ABOUT CATEGORIES AS POLYNOMIAL COMONOIDS ---------------------

// polynomial modules
constant symbol poly : Π [A : cat] (PA : mod Terminal_cat A) (B : cat), TYPE ;
// underlying profunctor of polynomial module
// symbol poly_mod : Π [A : cat] [PA : mod Terminal_cat A] [B : cat], poly PA B → mod (Elements_cat PA) B;
injective symbol poly_mod : Π [A : cat] [PA : mod Terminal_cat A] [B : cat], poly PA B → Π [I] (f : func I (Elements_cat PA)), mod I B;
rule $i ∘>> poly_mod $R $f ↪ poly_mod $R ($i ∘> $f);

// polynomial module substitution/composition ↘poly
// prafunctor semantics (non-internalized version) of substitution 
injective symbol ↘poly_base [A B : cat] [PA : mod Terminal_cat A] (R : poly PA B): 
      mod Terminal_cat B → mod Terminal_cat A
≔ λ PB, ((PB ⇐ (poly_mod R Id_func)) ⊗ (Unit_mod (Elements_proj_func PA) Id_func));
notation ↘poly_base infix left 70;
// substitution
constant symbol ↘poly : Π [A B X : cat] [PA : mod Terminal_cat A], Π (R : poly PA B), Π [PB : mod Terminal_cat B], Π (S : poly PB X),
poly (R ↘poly_base PB) X;
notation ↘poly infix left 70;

constant symbol ↘poly_intro_hom : Π [A B C : cat] [PA : mod Terminal_cat A], Π (R : poly PA B),
Π [PB : mod Terminal_cat B], Π (S : poly PB C), 
Π [I] [f : func I (Elements_cat PA)]   
(k : hom (Terminal_func I) (PB ⇐ (poly_mod R f) ) Id_func)
/* more relaxed/general than a : hom Id Unit(F,Id) G */
[G : func I A] (a : hom f (Unit_mod (Elements_proj_func PA) Id_func) G), 
Π [K : func I C], Π [H : func I B] (r : hom Id_func (poly_mod R f) H), 
   hom Id_func (poly_mod S (Elements_intro_func ((Eval_cov_hom_transf k) ∘' r))) K →
hom (Elements_intro_func (Tensor_cov_hom_hom _ k a)) (poly_mod (R ↘poly S) Id_func) K;


/*****************************************
* # ADJUNCTION OF FUNCTORS BETWEEN CATEGORIES
******************************************/

constant symbol adj : Π [R L : cat], func R L → func L R → TYPE;

// TODO: REVIEW HOW A SIMPLIFIED LESS-EXPRESSIVE VERSION OF EVERYTHING SHOULD BE POSSIBLE 
// (NO BUILT-IN SUBSTITUTIONS, NO BUILT-IN PULLBACKS.. IN YONEDA, FUNC, ADJUNCTIONS, ...) 
// AND HOW FAR STANDARD RESULTS ARE STILL EXPRESSIBLE

//REVIEW: the first/inner param Z seems required?
// (if yoneda ∘>'_(Z') has also extra pullback param)
constant symbol Adj_cov_hom : Π [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R]
(aj : adj LAdj_func RAdj_func), Π [I] (Z : func I L) [J] (M : func J I),
hom (M ∘> (Z ∘> RAdj_func)) (Unit_mod LAdj_func Z) M;

constant symbol Adj_con_hom : Π [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R]
(aj : adj LAdj_func RAdj_func), Π [I] (Z : func I R) [J] (N : func J I),
hom N (Unit_mod Z RAdj_func) (N ∘> (Z ∘> LAdj_func));

// these rules show both params of adjunction are ok/natural, 
// but the first/inner param Z seems required
rule (Adj_cov_hom $aj $Z _ /*≔Id_func*/) ∘>'_($Z') ∘' Func_cov_hom $Z' $F 
 ↪ Adj_cov_hom $aj ($Z' ∘> $Z) $F;
rule (Func_con_hom $Z' $F) '∘ ($Z')_'∘> (Adj_con_hom $aj $Z _ /*≔Id_func*/) 
 ↪ Adj_con_hom $aj ($Z' ∘> $Z) $F;

rule (Adj_cov_hom $aj $Z $M) ∘>'_(_ /*≔Id_func*/) ∘' Func_con_hom $M $F 
↪ Adj_cov_hom $aj $Z ($F ∘> $M);
rule (Func_cov_hom $M $F) '∘ (_ /*≔Id_func*/)_'∘> (Adj_con_hom $aj $Z $M) 
↪ Adj_con_hom $aj $Z ($F ∘> $M);

rule (Adj_cov_hom $aj $Z $N) ∘↓ $X ↪ Adj_cov_hom $aj $Z ($N <∘ $X);
rule (Adj_con_hom $aj $Z $N) ∘↓ $X ↪ Adj_con_hom $aj $Z ($X ∘> $N);

/* -----
* ## CONVERSION RULES FOR ADJUNCTION: ACCUMULATION */

//accumulation contravariant ; accumulation not really naturality, therefore can be dealt with generically

assert [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) [I] (Z : func I R)
  [J I1 I2 : cat] (X: func J I1) (X0: func I1 I) (Y: func J I2) (Y0 : func I2 I) 
  (g : hom X (Unit_mod X0 Y0) Y) J' (M: func J' I1) ⊢ eq_refl _ : τ (

 (M)_'∘>  (g '∘ ((X0)_'∘> (Adj_con_hom aj Z Y0)))
  =  ((M)_'∘>  g) ''∘ ((M ∘> X0)_'∘> (Adj_con_hom aj Z Y0)) );

//accumulation  covariant ; accumulation not really naturality, therefore can be dealt with generically

assert [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R]
(aj : adj LAdj_func RAdj_func) [I] (Z : func I R)
 [J I1 I2 : cat] (X: func J I1) (X0: func I1 I) (Y: func J I2) (Y0 : func I2 L) 
 (g : hom X (Unit_mod (X0 ∘> (Z ∘> LAdj_func)) Y0) Y) J' (M: func J' I2) ⊢ eq_refl _ : τ (

    (((Adj_con_hom aj Z X0) ∘>'_(Y0)) ∘' g) ∘>'_(M)
 =   ((Adj_con_hom aj Z X0) ∘>'_(Y0 <∘ M)) ∘'' (g ∘>'_(M)) );

/* -----
* ## CONVERSION RULES FOR ADJUNCTION: NATURALITY */

//TODO: ERASE this is actual naturality where commuation occurs, not mere accumulation, therefore canNOT be dealt with generically
//  symbol naturality2_con_cov : Π [L I : cat] [Z_LAdj_func : func I L] [Unit_mod_Z_RAdj_func : mod I L]
//  (Adj_con_hom_Z : hom Id_func Unit_mod_Z_RAdj_func Z_LAdj_func)
//   [J I1 I2 : cat] [X: func J I1] (X0: func I1 I) [Y: func J I2] (Y0 : func I2 I) 
//   (g : hom X (Unit_mod X0 Y0) Y) [J' : cat] (N : func J' I), /* N is more general */
 
//   (g '∘ ((X0)_'∘> ((Adj_con_hom_Z) ∘↓ Y0))) ∘>'_(Id_func)
//      ∘''  (( (Y ∘> Y0)_'∘> (Func_con_hom (Z_LAdj_func)) ∘↓ N))
//   = ((g '∘ ((X0)_'∘> (Id_hom Y0))) ∘>'_(N))
//             ''∘ ((X0)_'∘> ((Adj_con_hom_Z) ∘↓ N)) ;

// naturality (unit, covariant eq), similar with naturality (counit, contravariant eq)
// rule 
//WARNING subtle, g must be (hom Id_func _ _)
//        (@'∘ _ _ _ _ _ _ _ $Y _ $g  (($X0)_'∘> ((@Adj_con_hom _ _ $LAdj_func _ $aj _ $Z _ $Y0)))) ∘>'_(Id_func)
//        ∘'' (( ($Y ∘> $Y0)_'∘> (Func_con_hom ($Z ∘> $LAdj_func) $N)))
// ↪ (($g '∘ (($X0)_'∘> (Id_hom $Y0))) ∘>'_ ($N))
//    ''∘ (($X0)_'∘> ((Adj_con_hom $aj $Z $N) ));
rule
(( ($Y ∘> $Y0)_'∘> (Func_con_hom ($Z ∘> $LAdj_func) $N))) ''∘
((@'∘ _ _ _ _ _ _ _ $Y _ $g  (($X0)_'∘> ((@Adj_con_hom _ _ $LAdj_func _ $aj _ $Z _ $Y0)))) ∘>'_(Id_func))
       
 ↪ (($g '∘ (($X0)_'∘> (Id_hom $Y0))) ∘>'_ ($N))
   ''∘ (($X0)_'∘> ((Adj_con_hom $aj $Z $N) ));
   
// assert [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R] [aj : adj LAdj_func RAdj_func] [I] [Z : func I R]
//  [J I1 I2 : cat] [X: func J I1] [X0: func I1 I] [Y: func J I2] [Y0 : func I2 I] 
//  [g : hom X (Unit_mod X0 Y0) Y] [J' : cat] [N : func J' I] ⊢ eq_refl _ : τ (

//  (g '∘ ((X0)_'∘> (Adj_con_hom aj Z Y0))) ∘>'_(Id_func)
//     ∘''  (( (Y ∘> Y0)_'∘> (Func_con_hom (Z ∘> LAdj_func) N)))
//  = ((g '∘ ((X0)_'∘> (Id_hom Y0))) ∘>'_(N))
//            ''∘ ((X0)_'∘> (Adj_con_hom aj Z N)) );
assert [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R] [aj : adj LAdj_func RAdj_func] [I] [Z : func I R]
 [J I2 : cat] [X0: func J I] [Y: func J I2] [Y0 : func I2 I] 
 [g : hom Id_func (Unit_mod X0 Y0) Y] [J' : cat] [N : func J' I] ⊢ eq_refl _ : τ (

 (( (Y ∘> Y0)_'∘> (Func_con_hom (Z ∘> LAdj_func) N)))
  ''∘ (g '∘ ((X0)_'∘> (Adj_con_hom aj Z Y0))) ∘>'_(Id_func)  
 = ((g '∘ ((X0)_'∘> (Id_hom Y0))) ∘>'_(N))
           ''∘ ((X0)_'∘> (Adj_con_hom aj Z N)) );

//functoriality/naturality covariant     

assert  [L I : cat] [Z_LAdj_func : func I L]
  [J I1 I2 : cat] [X0: func J I] [Y: func J I2] [Y0 : func I2 I] 
  [g : hom Id_func (Unit_mod X0 Y0) Y] [J' : cat] [N : func J' I] ⊢ eq_refl _ : τ (
 
  (( (Y ∘> Y0)_'∘> (Func_con_hom (Z_LAdj_func) N)))
  ''∘ ((g '∘ ((X0)_'∘> ((Func_con_hom Z_LAdj_func Y0)))) ∘>'_(Id_func))
 = ((g '∘ ((X0)_'∘> (Id_hom Y0))) ∘>'_(N))
            ''∘ ((X0)_'∘> ((Func_con_hom Z_LAdj_func N))) );

// naturality (counit, covariant eq),  similar with naturality (unit, contravariant eq)
// rule ($d '∘ (($M)_'∘> (@Adj_cov_hom _ _ $F $G $aj _ $N _ $X))) ∘>'_($L) 
// ↪ (($d '∘ (($M)_'∘> (Func_cov_hom ($G <∘ $N) $X))) ∘>'_($L))
//           ''∘ (($M)_'∘> (Adj_cov_hom $aj ($N <∘ $L) Id_func)) ;
rule ($d '∘ (($M)_'∘> (@Adj_cov_hom _ _ $F $G $aj _ $N _ $X))) ∘>'_($L) 
↪ (($M)_'∘> (Adj_cov_hom $aj ($N <∘ $L) Id_func)) ∘''
(($d '∘ (($M)_'∘> (Func_cov_hom ($G <∘ $N) $X))) ∘>'_($L));

assert [C D : cat] [F : func D C] [G : func C D] [aj : adj F G] [C'] [N : func C' C] [I] [X : func I C']
  [E] [M : func E D] [J] [Z : func J E] [Y : func J I] (d : hom Z (Unit_mod M ((G <∘ N) <∘ X)) Y)
  [C''] [L : func C'' C']   ⊢ eq_refl _ : τ (

 (d '∘ ((M)_'∘> (Adj_cov_hom aj N X))) ∘>'_(L) 
= ((M)_'∘> (Adj_cov_hom aj (N <∘ L) Id_func)) ∘''
  ((d '∘ ((M)_'∘> (Func_cov_hom (G <∘ N) X))) ∘>'_(L)) );

// //TODO REVIEW IF SHOULD BE THIS REVERSED DIRECTION? nope rule redex has patterns, not registered, assertion fails
// rule (($M)_'∘> (@Adj_cov_hom _ _ $F $G $aj _ ($N <∘ $L) _ Id_func)) ∘''
// (($d '∘ (($M)_'∘> (Func_cov_hom ($G <∘ $N) $X))) ∘>'_($L))
// ↪ ($d '∘ (($M)_'∘> (@Adj_cov_hom _ _ $F $G $aj _ $N _ $X))) ∘>'_($L);
// assert [C D : cat] [F : func D C] [G : func C D] [aj : adj F G] [C'] [N : func C' C] [I] [X : func I C']
//   [E] [M : func E D] [J] [Z : func J E] [Y : func J I] (d : hom Z (Unit_mod M ((G <∘ N) <∘ X)) Y)
//   [C''] [L : func C'' C']   ⊢ eq_refl _ : τ (
// ((M)_'∘> (Adj_cov_hom aj (N <∘ L) Id_func)) ∘''
//   ((d '∘ ((M)_'∘> (Func_cov_hom (G <∘ N) X))) ∘>'_(L))
// = (d '∘ ((M)_'∘> (Adj_cov_hom aj N X))) ∘>'_(L) );


// assert [C D : cat] [F : func D C] [G : func C D] [aj : adj F G] [C'] [N : func C' C] [I] [X : func I C']
//   [E] [M : func E D] [J] [Z : func J E] [Y : func J I] (d : hom Z (Unit_mod M ((G <∘ N) <∘ X)) Y)
//   [C''] [L : func C'' C']   ⊢ eq_refl _ : τ (

// (d '∘ ((M)_'∘> (Adj_cov_hom aj N X))) ∘>'_(L) 
// = ((d '∘ ((M)_'∘> (Func_cov_hom (G <∘ N) X))) ∘>'_(L))
//           ''∘ ((M)_'∘> (Adj_cov_hom aj (N <∘ L) Id_func)) );


/* -----
* ## CONVERSION RULES FOR ADJUCTION: INVERSE BETA CANCELLATION*/


 // simple instance version , besides general version because no eta expansion of ϕ into (1)∘ϕ ...
 // “ϕ∘F(“G(f)∘γ”)”  =                  id∘1( 1(-)∘F ) 
  //TODO this rule and similars shoud be in applied version only... REVIEW EIHER BOTH VERSION OR REVERSE RULE $r '∘ ($rs ''∘ $st)
rule ((((@Adj_con_hom _ _ $LAdj_func $RAdj_func $aj _ $Z _ $M)) ∘>'_($W)) ∘' $f) 
'∘ (($Z)_'∘> ((Adj_cov_hom $aj $W Id_func)))
↪ ( (((Func_con_hom ($Z ∘> $LAdj_func) $M)) ∘>'_(_) ) ∘' $f) 
 '∘ (($Z ∘> $LAdj_func)_'∘> ((Func_cov_hom $W Id_func)));

rule (((@Adj_con_hom _ _ $LAdj_func $RAdj_func $aj _ $Z _ $M)) ∘>'_($N ∘> $W)) 
 ''∘ (($Z)_'∘> ((Adj_cov_hom $aj $W $N)))
↪ (((Func_con_hom ($Z ∘> $LAdj_func) $M)) ∘>'_($N ∘> $W) ) 
  ''∘ (($Z ∘> $LAdj_func)_'∘> ((Func_cov_hom $W $N)));

///WARNING M must be Id_func by new ''∘
// assert [L R I J I0 J0 : cat] [LAdj_func : func R L] [RAdj_func : func L R]
// (aj : adj LAdj_func RAdj_func) (Z : func I0 R) (M : func I I0) (N : func J J0) (W: func J0 L) ⊢ eq_refl _ : τ (
// (((Adj_con_hom aj Z M)) ∘>'_(N ∘> W)) ''∘ ((Z)_'∘> ((Adj_cov_hom aj W N)))
// = (((Func_con_hom (Z ∘> LAdj_func) M)) ∘>'_(N ∘> W) ) ''∘ ((Z ∘> LAdj_func)_'∘> ((Func_cov_hom W N))) );
// // : transf (Unit_mod (M ∘> (Z ∘> LAdj_func)) (N ∘> W)) M (Unit_mod (Z ∘> LAdj_func) W) N
assert [L R I J J0 : cat] [LAdj_func : func R L] [RAdj_func : func L R]
(aj : adj LAdj_func RAdj_func) (Z : func I R) (N : func J J0) (W: func J0 L) ⊢ eq_refl _ : τ (
(((Adj_con_hom aj Z Id_func)) ∘>'_(N ∘> W)) ''∘ ((Z)_'∘> ((Adj_cov_hom aj W N)))
= (((Func_con_hom (Z ∘> LAdj_func) Id_func)) ∘>'_(N ∘> W) ) ''∘ ((Z ∘> LAdj_func)_'∘> ((Func_cov_hom W N))) );
// : transf (Unit_mod (M ∘> (Z ∘> LAdj_func)) (N ∘> W)) M (Unit_mod (Z ∘> LAdj_func) W) N

// general version  SLOW HEAVY RULE - COMMENT THIS RULE DURING DEV, UNCOMMENT BEFORE COMPILATION (time lambdapi check -c test.lp)
 // f“ϕ∘F(“G(-)∘γ”g)”  =                  f"id∘1"( "1(-)∘F"g ) 
 //WARNING g must be (hom Id_func _ _)
rule (($g '∘ (($M')_'∘> (@Adj_con_hom _ _ $F $G $aj _ $M _ $Y))) ∘>'_($X' ∘> $X ∘> $N)) 
           ''∘ (($M' ∘> $M)_'∘> (@∘' _ _ _ _ _ _ $X' _ _ ((Adj_cov_hom $aj $N $X) ∘>'_($N')) $f))
↪ (($g '∘ ($M')_'∘> (Func_con_hom ($M ∘> $F) $Y)) ∘>'_($N <∘ $X <∘ $X')) 
           ''∘ (($M' ∘> $M ∘> $F)_'∘> ((Func_cov_hom $N $X) ∘>'_($N') ∘' $f));
assert [C D : cat] [F : func D C] [G : func C D] [aj : adj F G] 
[C'] [N : func C' C] [I] [X : func I C']
[C''] [N' : func C'' C'] [I'] [X' : func I' I] [Z : func I' C''] (f : hom X' (Unit_mod X N') Z)
[D'] [M : func D' D] [J] [Y : func J D']
[D''] [M' : func D'' D'] [Y' : func D'' J]  (g : hom Id_func (Unit_mod M' Y) Y')   ⊢ eq_refl _ : τ (

 ((g '∘ (M')_'∘> (Adj_con_hom aj M Y)) ∘>'_(N <∘ X <∘ X')) 
      ''∘ ((M' ∘> M)_'∘> ((Adj_cov_hom aj  N X) ∘>'_(N') ∘' f))
 =  ((g '∘ (M')_'∘> (Func_con_hom (M ∘> F) Y)) ∘>'_(N <∘ X <∘ X')) 
      ''∘ ((M' ∘> M ∘> F)_'∘> ((Func_cov_hom N X) ∘>'_(N') ∘' f)) );
//  : transf (Unit_mod (Y' ∘> (Y ∘> (M ∘> F))) (N <∘ X <∘ X'))  W (Unit_mod (M' ∘> M ∘> F) (N <∘ N')) Z
// assert [C D : cat] [F : func D C] [G : func C D] [aj : adj F G] 
// [C'] [N : func C' C] [I] [X : func I C']
// [C''] [N' : func C'' C'] [I'] [X' : func I' I] [Z : func I' C''] (f : hom X' (Unit_mod X N') Z)
// [D'] [M : func D' D] [J] [Y : func J D']
// [D''] [M' : func D'' D'] [J'] [Y' : func J' J] [W : func J' D''] (g : hom W (Unit_mod M' Y) Y')   ⊢ eq_refl _ : τ (

//  ((g '∘ (M')_'∘> (Adj_con_hom aj M Y)) ∘>'_(N <∘ X <∘ X')) 
//       ''∘ ((M' ∘> M)_'∘> ((Adj_cov_hom aj  N X) ∘>'_(N') ∘' f))
//  =  ((g '∘ (M')_'∘> (Func_con_hom (M ∘> F) Y)) ∘>'_(N <∘ X <∘ X')) 
//       ''∘ ((M' ∘> M ∘> F)_'∘> ((Func_cov_hom N X) ∘>'_(N') ∘' f)) );
// //  : transf (Unit_mod (Y' ∘> (Y ∘> (M ∘> F))) (N <∘ X <∘ X'))  W (Unit_mod (M' ∘> M ∘> F) (N <∘ N')) Z

//TODO REVIEW THIS ALT DIRECTION ... same problem of Id_func for $f
// rule (($M' ∘> $M)_'∘> (@∘' _ _ _ _ _ _ $X' _ _ ((Adj_cov_hom $aj $N $X) ∘>'_($N')) $f)) ∘''
//           (($g '∘ (($M')_'∘> (@Adj_con_hom _ _ $F $G $aj _ $M _ $Y))) ∘>'_($X' ∘> $X ∘> $N))
// ↪ (($M' ∘> $M ∘> $F)_'∘> ((Func_cov_hom $N $X) ∘>'_($N') ∘' $f)) ∘''
//          (($g '∘ ($M')_'∘> (Func_con_hom ($M ∘> $F) $Y)) ∘>'_($N <∘ $X <∘ $X'));


// beta cancelation, covariant eq   (small todo: general version “(f)∘ϕ∘F(“γ∘(-)”)”)
 // “ϕ∘F(“γ∘(g)”)” =            “1∘F(g)”   

rule ( ($M)_'∘> ((@Adj_con_hom _ _ $LAdj_func $RAdj_func  $aj _ $Z _ $N)) )
     ''∘ ( ($M ∘> $Z )_'∘> (Adj_cov_hom $aj Id_func Id_func) )
↪ ( ($M)_'∘> ((Func_con_hom ($Z ∘> $LAdj_func) $N)) );

assert [L R I J : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) Z (N : func I R) (M : func J R)  ⊢ eq_refl _ : τ (

 ( (M)_'∘> ((Adj_con_hom aj Z N)) )   ''∘ ( (M ∘> Z )_'∘> (Adj_cov_hom aj Id_func Id_func) )
=  ( (M)_'∘> ((Func_con_hom (Z ∘> LAdj_func) N)) ) );
 // : transf (Unit_mod M N) Id_func (Unit_mod (M ∘> (Z ∘> LAdj_func)) Id_func) ((Z ∘> LAdj_func) <∘ N)
 

/*****************************************
* # WEIGHTED LIMITS, RIGHT ADJOINTS PRESERVE WEIGHTED LIMITS
******************************************/

constant symbol limit_cov : Π [B J J' : cat] (F : func J B) (W : mod J' J) (F_⇐_W : func J' B), TYPE;
constant symbol limit_con: Π [B J J' : cat] (F : func J B) (W : mod J J') (W_⊗_F : func J' B), TYPE;

injective symbol limit_cov_univ_transf : Π [B J J' : cat] [W : mod J' J] [F : func J B] [F_⇐_W : func J' B]
 (isl : limit_cov F W F_⇐_W), Π [I : cat] (M : func I B),
 transf (((Unit_mod M F)) ⇐ W) Id_func (Unit_mod M F_⇐_W) Id_func;

injective symbol limit_con_univ_transf : Π [B J J' : cat] [W : mod J J'] [F : func J B] [W_⊗_F : func J' B]
 (isl : limit_con F W W_⊗_F), Π [I : cat] (M : func I B),
 transf (W ⇒ ((Unit_mod F M ))) Id_func (Unit_mod W_⊗_F M) Id_func;

injective symbol limit_cov_cone_transf : Π [B J J' : cat] [W : mod J' J] [F : func J B] [F_⇐_W : func J' B]
 (isl : limit_cov F W F_⇐_W), Π [I : cat] (M : func I B),
 transf (Unit_mod M F_⇐_W) Id_func (((Unit_mod M F)) ⇐ W) Id_func;

 //naturality
rule ($Z)_'∘> ($h '∘ limit_cov_cone_transf $isl $M) 
↪ (($Z)_'∘> $h) ''∘ limit_cov_cone_transf $isl ($Z ∘> $M);
rule ($Z)_'∘> ($f '∘  (limit_cov_univ_transf $isl $M)) 
↪ ( (_)_'∘> $f ) ''∘ (limit_cov_univ_transf $isl ($Z ∘> $M));

//beta
rule (limit_cov_cone_transf $isl $M) ∘'' (limit_cov_univ_transf $isl $M) ↪ Id_transf _ ;
//eta
rule (limit_cov_univ_transf $isl $M) ∘'' (limit_cov_cone_transf $isl $M) ↪ Id_transf _ ;

//  // right adjoint preserves weighted limit_covs
 
symbol righ_adjoint_preserves_limit_cov  [B J J' A : cat] [W : mod J' J] [F : func J B] [F_⇐_W : func J' B]
(isl : limit_cov F W F_⇐_W) [R : func B A] [L : func A B] (isa : adj L R) [I : cat] (M : func I A) :
transf ((Unit_mod M (F ∘> R)) ⇐ W) Id_func (Unit_mod M R <<∘ F_⇐_W) Id_func
≔ ((Adj_con_hom isa M Id_func) ∘>'_(F_⇐_W)) ∘''
((limit_cov_univ_transf isl (M ∘> L)) ∘'' (Imply_cov_transf ((M)_'∘> Adj_cov_hom isa F Id_func) (Id_transf W)) );


/*****************************************
* # DUALITY, COVARIANT VS CONTRAVARIANCE, LEFT ADJOINT PRESERVE WEIGHTED COLIMITS BY DUALITY
******************************************/

injective symbol Op_cat : cat → cat;

rule Op_cat (Op_cat $A) ↪ $A
with Op_cat (Terminal_cat) ↪ Terminal_cat ;

injective symbol Op_func : Π [A B: cat], func A B → func (Op_cat A) (Op_cat B);

rule Op_func (Op_func $F) ↪ $F
with Op_func Id_func ↪ Id_func
with Op_func ($F ∘> $G) ↪ ((Op_func $F) ∘> (Op_func $G));

rule Op_func (Terminal_func $A) ↪ (Terminal_func (Op_cat $A));

injective symbol Op_mod : Π [A B : cat], mod A B → mod (Op_cat B) (Op_cat A);

rule Op_mod (Op_mod $A) ↪ $A
with Op_mod (Unit_mod $F $G) ↪ (Unit_mod (Op_func $G) (Op_func $F)) 
with Op_mod ( $R ⊗ $S ) ↪ (Op_mod $S) ⊗ (Op_mod $R)  
with Op_mod ( $R ⇐ $S ) ↪ (Op_mod $S) ⇒ (Op_mod $R) 
with Op_mod ( $R ⇒ $S ) ↪ (Op_mod $S) ⇐ (Op_mod $R) ;

rule Op_mod ($F ∘>> $R) ↪ ((Op_mod $R) <<∘ (Op_func $F))
with Op_mod ($R <<∘ $G) ↪ ((Op_func $G) ∘>> (Op_mod $R));

injective symbol Op_hom : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] (r : hom F R G), hom (Op_func G) (Op_mod R) (Op_func F);

rule Op_hom (Op_hom $A) ↪ $A
with Op_hom (Id_hom $F) ↪ (Id_hom (Op_func $F))
with Op_hom (Func_con_hom $Z $F) ↪ Func_cov_hom (Op_func $Z) (Op_func $F)
with Op_hom (Func_cov_hom $Z $F) ↪ Func_con_hom (Op_func $Z) (Op_func $F);

rule Op_hom ($r ∘↓ $H) ↪ (Op_hom $r) ∘↓ (Op_func $H);

injective symbol Op_transf : Π [X Y X' Y': cat] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y], 
 transf R xx' R' yy' → transf (Op_mod R) (Op_func yy') (Op_mod R') (Op_func xx');

rule Op_transf (Op_transf $A) ↪ $A
with Op_transf (Id_transf $R) ↪ (Id_transf (Op_mod $R));

//TODO: CORRECT IT
//rule Op_transf (Tensor_cov_transf $rr $ss) ↪ (Tensor_cov_transf (Op_transf $ss) (Op_transf $rr));
// rule Op_transf (Tensor_cov_transf $M $rr $ss) ↪ (Tensor_cov_transf (Op_func $M) (Op_transf $ss) (Op_transf $rr));

rule Op_transf (($M)_'∘> $r) ↪ (Op_hom $r) ∘>'_ (Op_func $M);
rule Op_transf ($r ∘>'_ ($M)) ↪ (Op_func $M) _'∘> (Op_hom $r);

rule Op_hom ($s '∘ $st) ↪ (Op_transf $st) ∘' (Op_hom $s)
with Op_hom ($st ∘' $s) ↪ (Op_hom $s) '∘ (Op_transf $st);

rule Op_transf ($rs ''∘ $st) ↪ (Op_transf $st) ∘'' (Op_transf $rs);
rule Op_transf ($rs ∘'' $st) ↪ (Op_transf $st) ''∘ (Op_transf $rs);

/** ** duality for fibrations of categories */

injective symbol Op_catd : Π [X : cat] (A : catd X), catd (Op_cat X);
injective symbol Op_isFibration_cov : Π [X : cat] [A : catd X], isFibration_con A → isFibration_cov (Op_catd A);
injective symbol Op_isFibration_con : Π [X : cat] [A : catd X], isFibration_cov A → isFibration_con (Op_catd A);

rule Op_catd (Op_catd $A) ↪ $A;
rule Op_isFibration_cov (Op_isFibration_con $A_isf) ↪ $A_isf
with Op_isFibration_con (Op_isFibration_cov $A_isf) ↪ $A_isf;

rule Op_catd (Fibre_catd $A $x) ↪ (Fibre_catd (Op_catd $A) (Op_func $x))
with Op_catd (Terminal_catd $X) ↪ Terminal_catd (Op_cat $X)
with Op_catd (Comma_con_catd $R $BB) ↪ (Comma_cov_catd  (Op_catd $BB) (Op_mod $R))
with Op_catd (Comma_cov_catd $AA $R) ↪ (Comma_con_catd (Op_mod $R) (Op_catd $AA));

injective symbol Op_funcd : Π [X Y : cat] [A : catd X] [F : func X Y] [B : catd Y], funcd A F B → funcd (Op_catd A) (Op_func F) (Op_catd B);

rule Op_funcd (Op_funcd $F) ↪ $F
with Op_funcd (Id_funcd) ↪ (Id_funcd)
with Op_funcd ($F ∘>d $G) ↪ ((Op_funcd $F) ∘>d (Op_funcd $G)) ;

rule Op_funcd (Terminal_funcd $A $xy) ↪ (Terminal_funcd (Op_catd $A) (Op_func $xy) );

rule Op_funcd (Fibre_intro_funcd $A $x $i $FF) ↪ (Fibre_intro_funcd (Op_catd $A) (Op_func $x) (Op_func $i) (Op_funcd $FF))
with Op_funcd (Fibre_elim_funcd $A $x) ↪ (Fibre_elim_funcd (Op_catd $A) (Op_func $x));

/** ** duality for fibrations of modules */

injective symbol Op_modd : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y]
(RR : modd A R B), modd (Op_catd B) (Op_mod R) (Op_catd A);

rule Op_modd (Op_modd $RR) ↪ $RR
with Op_modd (Unit_modd $FF $GG) ↪ (Unit_modd (Op_funcd $GG) (Op_funcd $FF)) 
with Op_modd ( Terminal_modd $R ) ↪ Terminal_modd (Op_mod $R)
with Op_modd ( Fibre_transf_modd $RR $sr ) ↪ Fibre_transf_modd (Op_modd $RR) (Op_transf $sr) 
with Op_modd ( $RR ⊗d $SS ) ↪ (Op_modd $SS) ⊗d (Op_modd $RR) ;

rule Op_modd ($F ∘>>d $R) ↪ ((Op_modd $R) d<<∘ (Op_funcd $F))
with Op_modd ($R d<<∘ $G) ↪ ((Op_funcd $G) ∘>>d (Op_modd $R));

rule Op_modd (Fibre_modd $RR $sr) ↪ Fibre_modd (Op_modd $RR) (Op_transf $sr) ;

injective symbol Op_homd: Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
[A : catd X] [B : catd Y] [II : catd I] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B],
homd r FF RR GG → homd (Op_hom r) (Op_funcd GG) (Op_modd RR) (Op_funcd FF);

rule Op_homd (Op_homd $F) ↪ $F
with Op_homd (Id_homd $F) ↪ (Id_homd (Op_funcd $F))
with Op_homd (Func_con_homd $Z $F) ↪ Func_cov_homd (Op_funcd $Z) (Op_funcd $F)
with Op_homd (Func_cov_homd $Z $F) ↪ Func_con_homd (Op_funcd $Z) (Op_funcd $F);
rule Op_homd ($r ∘↓d $H) ↪ (Op_homd $r) ∘↓d (Op_funcd $H);

injective symbol Op_transfd: Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y]
[r : transf R xx' R' yy'] [RR : modd A R B] [FF : funcd A xx' A'] [RR' : modd A' R' B'] [GG : funcd B yy' B'],
 transfd r RR FF RR' GG → transfd (Op_transf r) (Op_modd RR) (Op_funcd GG) (Op_modd RR') (Op_funcd FF);

rule Op_transfd (Op_transfd $rr) ↪ $rr
with Op_transfd (Id_transfd $RR) ↪ (Id_transfd (Op_modd $RR));

rule Op_transfd (Terminal_transfd $RR $t_) ↪ Terminal_transfd (Op_modd $RR) (Op_transf $t_);

rule Op_transfd (($MM)_'∘>d $rr) ↪ (Op_homd $rr) ∘>d'_ (Op_funcd $MM);
rule Op_transfd ($rr ∘>d'_ ($MM)) ↪ (Op_funcd $MM) _'∘>d (Op_homd $rr);

rule Op_homd ($s '∘d $st) ↪ (Op_transfd $st) ∘d' (Op_homd $s)
with Op_homd ($st ∘d' $s) ↪ (Op_homd $s) '∘d (Op_transfd $st);

rule Op_transfd ($rs ''∘d $st) ↪ (Op_transfd $st) ∘d'' (Op_transfd $rs);

/** ** duality for universe */

rule Op_cat (Universe_cov_cat) ↪ Universe_con_cat
// this inverse necessary? yes for confluence and for the rule for Op_catd below
with Op_cat (Universe_con_cat) ↪ Universe_cov_cat;

rule Op_catd (Universe_cov_catd) ↪ Universe_con_catd
with Op_catd (Universe_con_catd) ↪ Universe_cov_catd;

rule Op_isFibration_cov (Universe_con_isFibration_con) ↪ Universe_cov_isFibration_cov
with Op_isFibration_con (Universe_cov_isFibration_cov) ↪ Universe_con_isFibration_con;

rule Op_func (Universe_cov_func $A $A_isf) ↪ (Universe_con_func (Op_catd $A) (Op_isFibration_con $A_isf))
with Op_func (Universe_con_func $A $A_isf) ↪ Universe_cov_func (Op_catd $A) (Op_isFibration_cov $A_isf);

rule Op_funcd (Universe_cov_funcd $A $A_isf) ↪ Universe_con_funcd (Op_catd $A) (Op_isFibration_con $A_isf)
with Op_funcd (Universe_con_funcd $A $A_isf) ↪ Universe_cov_funcd (Op_catd $A) (Op_isFibration_cov $A_isf);

/** ** duality for adjunctions */

injective symbol Op_adj : Π [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R]
(aj : adj LAdj_func RAdj_func), adj (Op_func RAdj_func) (Op_func LAdj_func);

rule Op_adj (Op_adj $aj) ↪ $aj;

rule Op_hom (Adj_cov_hom $aj $Z $X) ↪ Adj_con_hom (Op_adj $aj) (Op_func $Z) (Op_func $X);

/* -----
* ## DUALITY FOR LIMITS: COMPUTATION THAT LEFT ADJOINTS PRESERVE COLIMITS VIA DUALITY */

injective symbol Op_limit_con : Π [B J J' : cat] [W : mod J' J] [F : func J B] [F_⇐_W : func J' B]
(isl : limit_cov F W F_⇐_W), limit_con (Op_func F) (Op_mod W) (Op_func F_⇐_W);
injective symbol Op_limit_cov : Π [B J J' : cat] [W : mod J J'] [F : func J B] [W_⊗_F : func J' B]
(isl : limit_con F W W_⊗_F), limit_cov (Op_func F) (Op_mod W) (Op_func W_⊗_F);

rule Op_limit_con (Op_limit_cov $isl) ↪ $isl
with Op_limit_cov (Op_limit_con $isl) ↪ $isl ;

rule (Op_transf (limit_cov_univ_transf $isl $M) ) ↪ limit_con_univ_transf (Op_limit_con $isl) (Op_func $M);

// assert [B J0 J J' A : cat] [K : func J J0] [W : mod J' J] [F : func J0 B] [F_⇐_W : func J' B]
// (isl : limit_cov K F W F_⇐_W) [R : func B A] [L : func A B] (isa : adj L R) [I : cat] (M : func I A) ⊢
// Op_transf (righ_adjoint_preserves_limit_cov isl isa M) :
// transf (⇒ (Op_mod W) (Op_func K) ((Op_func F ∘> Op_func R) ∘>> (Unit_mod0 (Op_cat A) <<∘ Op_func M))) 
//          Id_func ((Op_func F_⇐_W ∘> Op_func R) ∘>> (Unit_mod0 (Op_cat A) <<∘ Op_func M)) Id_func;
assert [B J J' A : cat] [W : mod J' J] [F : func J B] [F_⇐_W : func J' B]
(isl : limit_cov F W F_⇐_W) [R : func B A] [L : func A B] (isa : adj L R) [I : cat] (M : func I A) ⊢
Op_transf (righ_adjoint_preserves_limit_cov isl isa M) :
transf ((Op_mod W) ⇒ ( (Unit_mod (Op_func F ∘> Op_func R) (Op_func M)))) 
         Id_func ((Unit_mod (Op_func F_⇐_W ∘> Op_func R) (Op_func M))) Id_func;

assert [B J J' A : cat] [W : mod J J'] [F : func J B] [W_⊗_F : func J' B]
(isl : limit_con F W W_⊗_F) [R : func A B] [L : func B A] (isa : adj L R) [I : cat] (M : func I A) ⊢
Op_transf (righ_adjoint_preserves_limit_cov (Op_limit_cov isl) (Op_adj isa) (Op_func M)) :
transf (Op_mod ((Unit_mod (Op_func M) (Op_func F ∘> Op_func L)) ⇐ (Op_mod W)))
   (Op_func Id_func) (Op_mod (Unit_mod (Op_func M) (Op_func L) <<∘ Op_func W_⊗_F)) (Op_func Id_func) ;

symbol left_adjoint_preserves_limit_con [B J J' A : cat] [W : mod J J'] [F : func J B] [W_⊗_F : func J' B]
(isl : limit_con F W W_⊗_F) [R : func A B] [L : func B A] (isa : adj L R) [I : cat] (M : func I A) :
  transf (W ⇒ (Unit_mod (F ∘> L) M)) Id_func (W_⊗_F ∘>> Unit_mod L M) Id_func
  ≔ Op_transf (righ_adjoint_preserves_limit_cov (Op_limit_cov isl) (Op_adj isa) (Op_func M));


/******************************************

Short description (possibly outdated):

Re: [Agda] position in Deducteam — Lawvere/Dosen session on categorial logic/programming @ CT2023

Salut Louis Auguste « L'Enfermé » Blanqui,

  A new implementation of dependent types via Dosen's substructural categorial programming: example of the Yoneda lemma for fibrations

This closes the open problem of implementing a dependent-types computer for category theory, where types are categories and dependent types are fibrations of categories. The basis for this implementation are the ideas and techniques from Kosta Dosen's book « Cut-elimination in categories » (1999), which essentially is about the substructural logic of category theory, in particular about how some good substructural formulation of the Yoneda lemma allows for computation and automatic-decidability of categorial equations.

The core of dependent types/fibrations in category theory is the Lawvere's comma/slice construction and the corresponding Yoneda lemma for fibrations (https://stacks.math.columbia.edu/tag/0GWH), thereby its implementation essentially closes this open problem also investigated by Cisinski's directed types or Garner's 2-dimensional types. What qualifies as a solution is subtle and the thesis here is that Dosen's substructural techniques cannot be bypassed.

In summary, this text implements, using Blanqui's LambdaPi metaframework software tool, an (outer) cut-elimination in the double category of fibred profunctors with (inner) cut-eliminated adjunctions. The outer cut-elimination essentially is a new functorial lambda calculus via the « dinaturality » of evaluation and the monoidal bi-closed structure of profunctors, without need for multicategories because (outer) contexts are expressed via dependent types. This text also implements (higher) inductive datatypes such as the join-category (interval simplex), with its introduction/elimination/computation rules. This text also implements Sigma-categories/types and categories-of-functors and more generally Pi-categories-of-functors, but an alternative more-intrinsic formulation using functors fibred over spans or over Kock's polynomial-functors will be investigated. This text also implements a dualizing Op operations, and it can computationally-prove that left-adjoint functors preserve profunctor-weighted colimits from the proof that right-adjoint functors preserve profunctor-weighted limits. This text also implements a grammatical (univalent) universe and the universal fibration classifying small fibrations, together with the dual universal opfibration. Finally, there is an experimental implementation of covering (co)sieves towards grammatical sheaf cohomology and towards a description of algebraic geometry's schemes in their formulation as locally affine ringed sites (structured topos), instead of via their Coquand's formulation as underlying topological space...

References:

[1] Dosen-Petric: Cut Elimination in Categories 1999; 
[2] Proof-Theoretical Coherence 2004; 
[3] Proof-Net Categories 2005; 
[4] Coherence in Linear Predicate Logic 2007; 
[5] Coherence for closed categories with biproducts 2022 
[6] Cut-elimination in the double category of fibred profunctors with inner cut-eliminated adjunctions: 
https://github.com/1337777/cartier/blob/master/cartierSolution13.lp 
[7] Pierre Cartier

Subscribe for live updates, WorkSchool365.com : https://www.youtube.com/@workschool365

FAQ:

* How is « substructural » contrasted vs « synthetic » ? The substructural Yoneda lemma for fibrations is expressed via a blend of the universality/introduction rule of the transported/pulledback objects inside fibred categories:

  constant symbol Fibration_con_intro_homd : Π [I X X'  : cat] [x'x : func X' X] (G : func X I) [KK : catd X'] [F : func X' I] [II : catd I] (II_isf : isFibration_con II) (FF : funcd KK F II) (f : hom x'x (Unit_mod G Id_func) F) [X'0 : cat] [x'0x : func X'0 X] [X'' : cat] [x''x' : func X'' X'] [x''x'0 : func X'' X'0] (x'0x' :  hom x''x'0 (Unit_mod x'0x x'x) x''x') [JJ : catd X'0] (MM : funcd JJ x'0x (Fibre_catd II G)) [HH : funcd (Fibre_catd KK x''x') x''x'0 JJ],
homd ((x'0x' '∘ ((x'0x)_'∘> f))) HH (Unit_modd (MM ∘>d (Fibre_elim_funcd II G)) Id_funcd) ((Fibre_elim_funcd KK (x''x')) ∘>d FF) →  
homd x'0x' HH (Unit_modd MM (Fibration_con_funcd G II_isf FF f)) (Fibre_elim_funcd KK (x''x')) ;

together with the composition operation (in Yoneda formulation) inside fibred categories:

  constant symbol ∘>d'_ : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G] [A : catd X] [B : catd Y] [II] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B], homd r FF RR GG → 
Π [J: cat] [M : func J Y] [JJ : catd J] (MM : funcd JJ M B), 
transfd ( r ∘>'_(M) ) (Unit_modd GG MM) FF (RR d<<∘ MM ) Id_funcd;                

* How is « J-rule arrow induction » contrasted vs « fibrational transport » ? The above intrinsic/structural universality formulation comes with a corresponding reflected/internalized algebra formulation, which is the comma category where the J-rule elimination ("equality/path/arrow induction") occurs. Similarly, pullbacks have a universal formulation (fibre of fibration), an algebraic formulation (composition of spans), or mixed (product of fibration-objects in the slice category).

  constant symbol Comma_con_intro_funcd : Π [A B I : cat] [R : mod A B] (BB : catd B) [x : func I A] [y : func I B] (r : hom x R y),
funcd (Fibre_catd BB y) x (Comma_con_catd R BB);

  constant symbol Comma_con_elim_funcd : Π [I X : cat] (G : func X I)  [II : catd I] (II_isf : isFibration_con II) [KK : catd I] (FF : funcd KK Id_func II), 
funcd (Comma_con_catd (Unit_mod G Id_func) KK) G II;

* Are substitutions explicit or intrinsic/structural? Ordinary (non-fibred) cut-elimination considers pairs of composable arrows p : X → Y then q : Y → Z, but fibred cut-elimination should also consider pairs of arrows p : X → f*Y then q : g*Y → Z, where f*Y is the pullback of Y along f, and such a pair is not manifestly/grammatically/syntactically-composable but only semantically-composable as g'*p : g'*X → g'*(f*Y) then f'*q : f'*(g*Y) → f'*Z, where f' = g*f is the pullback of f along g and g' = f*g is the pullback of g along f. The remedy is to make those pullback intrinsic/implicit in the implementation's grammar, so that p : X → f*Y is really notation for a judgment with 3 parameters X, Y and f, which can be read as « p is a fibred arrow forward-above the arrow f », and similarly q : g*Y → Z is read as « q is a fibred arrow backward-above the arrow g », and more generally r : g*X → f*Z is read as « r is a fibred arrow above the span of arrows g backward with f forward ». Ultimately it should be possible to express arrows fibred over polynomial-functors, so that the distributivity (ΠΣ = ΣΠε*) in the composition of polynomial-functors is intrinsic in the implementation's grammar... Finally, all of these intrinsic structures are reflected/internalized as an explicit substitution/pullback-type-former for any fibration.

* What is the difference between the Pi-type of sections and the category-of-functors? Ordinary Pi/product-types consider only the sections of some fibration, but Pi-categories should consider all the category-of-functors to some fibration, this leads to the new construction of Pi-category-of-functors. The preliminary implementation in this text does not yet use the more-intrinsic formulation using functors fibred-above-a-span of functors. It should be noted that Sigma/sum-categories can be already intrinsically-implemented using only functors fibred-forward-above a single functor.

* And why profunctors (of sets)? The primary motivation is that they form a monoidal bi-closed double category (functorial lambda calculus). Another motivation is that the subclass of fibrations called discrete/groupoidal fibrations can only be computationally-recognized/expressed instead via (indexed) presheaves/profunctors of sets. And the comma construction is how to recover the intended discrete fibration. Ultimately profunctors enriched in preorders/quantales instead of mere sets could be investigated (Tholen's TV, lol).

* What is a fibred profunctor anyway? The comma/slice categories are only fibred categories (of triangles of arrows fibred by their base), not really fibred profunctors. One example of fibred profunctor from the coslice category to the slice category is the set of squares fibred by their diagonal which witnesses that this square is constructed by pasting two triangles. This text implements such fibred profunctor of (cubical) squares (thereby validating the hypothesis that computational-cubes should have connections/diagonals...). For witnessing the (no-computational-content) pasting along the diagonal, this implementation uses for the first time the LambdaPi-metaframework's equality predicate which internally-reflects all the conversion-rules; in particular the implementation uses here the categorial-associativity equation axiom, which is a provable metatheorem which must *not* be added as a rewrite rule!

*/

/* voila */
