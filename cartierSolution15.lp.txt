/* https://github.com/1337777/cartier/blob/master/cartierSolution15.lp 
https://github.com/1337777/cartier/blob/master/Kosta_Dosen_outline_alt.pdf

Kosta Dosen's functorial programming: « m— » (read as « emdash » or « modos »), a new proof assistant for schemes.
  A computational logic (co-inductive) interface for algebraic geometry schemes.

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

OUTLINE OF cartierSolution15.lp :

# SECTION 1 : POLYNOMIAL MODULES

# SECTION 2 : CATEGORIES AS POLYNOMIAL COMONOIDS

*/

/* Short description (possibly outdated):

https://github.com/1337777/cartier/blob/master/cartierSolution15.lp
https://github.com/1337777/cartier/blob/master/Kosta_Dosen_polynomial_univalence.pdf

Kosta Dosen's univalent polynomial functorial programming

DRAFT OUTLINE:

Kosta Dosen’s book « Cut-elimination in categories » (1999) is how some good substructural formulation of the Yoneda lemma, via profunctors, allows for computation and automatic-decidability of categorial equations. For example, the profunctor C[F-,_] is a distinct computer type than the hom-profunctor C[-,_] of the category C applied to outer objects of the form F- ...

This new stricter typing discipline is still successful to compute with polynomials (morphisms of polynomial-bicomodules along cofunctors of categories, substitution of polynomials, and their prafunctor semantics) via their underlying profunctors. It is conjectured that these computations can be extended to analytic functors and their automatic differentiation (via linear-logic's exponential comonad on the underlying profunctors) in reverse-mode (differential categories) for gradient-based neural-learning...

And now this updated implementation of fibred profunctors has a draft application to inductively-constructed covering sieves and sheaf topology: a sieve is a fibred profunctor dependent over the hom-profunctor; and the Yoneda action and lemma (gluing) still holds when the hom-profunctor (the total sieve) is replaced by any covering sieve and the presheaf is replaced by a sheaf.
*/

require open modos.cartierSolution13;


// discrete/groupoid as a category


/*****************************************
* # SECTION 1 : POLYNOMIAL MODULES
******************************************/

//TODO: UPDATE FROM THE VERSION IN cartierSolution13.lp AND ERASE THIS SECTION

// polynomial modules
constant symbol poly : Π [A : cat] (PA : mod Terminal_cat A) (B : cat), TYPE ;
constant symbol poly_Type : Π [A : cat] (PA : mod Terminal_cat A) (B : cat), Type ;
rule τ (@poly_Type $A $PA $B) ↪ @poly $A $PA $B;
// underlying profunctor of polynomial module
symbol poly_mod : Π [A : cat] [PA : mod Terminal_cat A] [B : cat], poly PA B → mod (Elements_cat PA) B;

// polynomial module substitution/composition ↘poly
// prafunctor semantics (non-internalized version) of substitution 
symbol ↘poly_base [A B : cat] [PA : mod Terminal_cat A] (R : poly PA B): 
      mod Terminal_cat B → mod Terminal_cat A
≔ λ PB, ((PB ⇐ (poly_mod R)) ⊗ (Unit_mod (Elements_proj_func PA) Id_func));
notation ↘poly_base infix left 70;
// substitution
constant symbol ↘poly : Π [A B X : cat] [PA : mod Terminal_cat A], Π (R : poly PA B), Π [PB : mod Terminal_cat B], Π (S : poly PB X),
poly (R ↘poly_base PB) X; 
notation ↘poly infix left 70;

constant symbol ↘poly_intro_hom : Π [A B C : cat] [PA : mod Terminal_cat A], Π (R : poly PA B),
Π [PB : mod Terminal_cat B], Π (S : poly PB C), 
Π [I] [F : func I A] [f : hom (Terminal_func I) PA F]   
(k : hom (Terminal_func I) (PB ⇐ ((Elements_intro_func f) ∘>> (poly_mod R)) ) Id_func)
[G : func I A] (a : hom (Elements_intro_func f) (Unit_mod (Elements_proj_func PA) Id_func) G) /* more relaxed/general than a : hom Id Unit(F,Id) G */,  
Π [K : func I C], Π [H : func I B] (r : hom Id_func ((Elements_intro_func f) ∘>> (poly_mod R)) H),
   hom Id_func (((Elements_intro_func ((Eval_cov_hom_transf k) ∘' r))) ∘>> (poly_mod S)) K →
hom (Elements_intro_func (Tensor_cov_hom_hom _ k a)) (poly_mod (R ↘poly S)) K;


/*****************************************
* # SECTION 2 : CATEGORIES AS POLYNOMIAL COMONOIDS
******************************************/

constant symbol cofunc : Π (A B : cat), TYPE ;
constant symbol cofunc_Type : Π (A B : cat), Type ;
rule τ (@cofunc_Type $A $B) ↪ @cofunc $A $B ;

constant symbol Id_cofunc : Π [A : cat], cofunc A A ;
symbol ∘>c : Π [A B C: cat], cofunc A B → cofunc B C → cofunc A C;
notation ∘>c infix left 90;

rule $X ∘>c ($G ∘>c $H) ↪ ($X ∘>c $G) ∘>c $H
with $F ∘>c Id_cofunc ↪ $F
with Id_cofunc ∘>c $F ↪ $F;

symbol ∘>cb : Π [B C: cat] [I : Type], func (type_cat I) B → cofunc B C → func (type_cat I) C;
notation ∘>cb infix right 80;

rule @∘> (type_cat _) _ _ $X ($G ∘>cb $H) ↪ ($X ∘> $G) ∘>cb $H
with $F ∘>cb Id_cofunc ↪ $F
with $X ∘>cb ($F ∘>c $G) ↪ ($X ∘>cb $F) ∘>cb $G;

symbol cofunc_transp_func : Π [A B : cat] (M : cofunc A B) [I : Type] [F : func (type_cat I) B] 
[I' : Type] [X : func (type_cat I) (type_cat I')] (G : func (type_cat I') A),
hom X (Unit_mod (G ∘>cb M) Id_func) F → func (type_cat I) A;

rule (@cofunc_transp_func _ _ $M _ $F _ _ $G $h) ∘>cb $M  ↪  $F ;

constant symbol cofunc_transp :  Π [A B : cat] (M : cofunc A B) [I : Type] [F : func (type_cat I) B]
[I' : Type] [X : func (type_cat I) (type_cat I')] (G : func (type_cat I') A),
Π (h : hom X (Unit_mod (G ∘>cb M) Id_func) F),  
hom X (Unit_mod G Id_func) (cofunc_transp_func M G h);

rule (cofunc_transp_func $M (cofunc_transp_func $M $G $h) $h')
↪ (cofunc_transp_func $M $G (($h ∘>'_(_)) ∘' $h'));

assert [A B : cat] (M : cofunc A B) [I : Type] [F : func (type_cat I) B]
[I' : Type] [X : func (type_cat I) (type_cat I')] (G : func (type_cat I') A)
 (h : hom X (Unit_mod (G ∘>cb M) Id_func) F)
[I1] [X'] [F' : func (type_cat I1) B] (h' : hom X' (Unit_mod F Id_func) F') ⊢ eq_refl _ : τ (
(cofunc_transp_func M (cofunc_transp_func M G h) h')
= (cofunc_transp_func M G ((h ∘>'_ Id_func) ∘' h')));

rule (cofunc_transp $M $G $h ∘>'_(_) ) ∘' (cofunc_transp $M /*DO NOT: (cofunc_transp_func $M $G $h)*/ _ $h')
↪ cofunc_transp $M $G ($h ∘>'_(_)  ∘' $h');

assert [A B : cat] (M : cofunc A B) [I : Type] [F : func (type_cat I) B]
[I' : Type] [X : func (type_cat I) (type_cat I')] (G : func (type_cat I') A)
 (h : hom X (Unit_mod (G ∘>cb M) Id_func) F)
 [I1] [X'] [F' : func (type_cat I1) B] (h' : hom X' (Unit_mod F Id_func) F') ⊢ eq_refl _ : τ (
(cofunc_transp M G h ∘>'_(_) ) ∘' (cofunc_transp M (cofunc_transp_func M G h) h')
= cofunc_transp M G (h ∘>'_(_)  ∘' h'));

//memo: forward app
constant symbol cotransf_base : Π [A' A B' B: cat], mod A' B' → cofunc A' A → mod A B → cofunc B' B → TYPE ;
//memo: reverse app
constant symbol cotransf : Π [A' B' A B: cat] [PA' : mod Terminal_cat A'] [PA : mod Terminal_cat A], 
poly PA' B' → Π [F : cofunc A' A] (f : cotransf_base PA' Id_cofunc PA F), poly PA B → cofunc B' B → TYPE ;

//TODO update ealier file with this more general accumulation
rule $m '∘ ($M)_'∘> ($g '∘ $t)
↪ ($m '∘ ($M)_'∘> $g) '∘ ($M 1∘>> $t);
// alt: the other pointwide version necessary?
// rule ($M)_'∘> ($g '∘ $t)
// ↪ (($M)_'∘> $g) ''∘ ($M 1∘>> $t);
// assert [A B' B I : cat] [S : mod A B'] [T : mod A B]
// [X : func I A] [Y : func I B']  [G : func B' B]
// (h : hom X S Y) (t : transf S Id_func T G) [J] (M : func J A) ⊢ eq_refl _ : τ (
// (M)_'∘> (h '∘ t)  = ((M)_'∘> h)  ''∘  (M 1∘>> t) ); //→ hom X T (G <∘ Y);
assert [A B' B I : cat] [S : mod A B'] [T : mod A B]
[X : func I A] [Y : func I B']  [G : func B' B]
(h : hom X S Y) (t : transf S Id_func T G) [J] (M : func J A)
 [J'] [K : func J' J] [L : func J' I] (m : hom K (Unit_mod M X) L) ⊢ eq_refl _ : τ (
m '∘ (M)_'∘> (h '∘ t) = ( m '∘ (M)_'∘> h)  '∘  (M 1∘>> t) );

symbol '∘cb : Π [A B' B : cat] [I : Type] [S : mod A B'] [T : mod A B]
[X : func (type_cat I) A] [Y : func (type_cat I) B']  [G : cofunc B' B],
hom X S Y → cotransf_base S Id_cofunc T G → hom X T (Y ∘>cb G);
notation '∘cb infix right 80;

symbol ''∘cb [ B'' B' A B : cat] [R : mod A B''] [S : mod A B'] [T : mod A B] 
[Y : cofunc B'' B']  [G : cofunc B' B] :
cotransf_base R Id_cofunc S Y → cotransf_base S Id_cofunc T G →  cotransf_base R Id_cofunc T (Y ∘>c G);
notation ''∘cb infix right 80;

rule  $rs ''∘cb ($st ''∘cb $tu) ↪ ($rs ''∘cb $st) ''∘cb $tu;
rule  $r '∘cb ($rs ''∘cb $st)
↪ ($r '∘cb $rs) '∘cb $st;

symbol 1∘>>cb : Π [X Y Y' : cat] [G : cofunc Y Y'] [R' : mod X Y'] [R : mod X Y] [Z : cat] (H : func Z X) (r : cotransf_base R Id_cofunc R' G) , 
cotransf_base (H ∘>> R) Id_cofunc (H ∘>> R') G;
notation 1∘>>cb infix right 80;

rule Id_func 1∘>>cb  $t  ↪ $t 
with $K 1∘>>cb ($H 1∘>>cb $t) ↪ ($K ∘> $H) 1∘>>cb $t; 

rule @∘'  _ _ _ (type_cat _) _ _ _ _ _ ((@'∘cb _ _ _ _ _ _ _ $Y $G $h $t) ∘>'_(Id_func)) $k ↪
($h ∘>'_(Id_func) ∘' (cofunc_transp $G $Y $k)) '∘cb $t;

rule @∘↓ _ _ _ (type_cat _) _ _ _  ($a '∘cb $f)  $F  ↪ ($a ∘↓ $F) '∘cb $f;

assert [A B' B : cat] [I : Type] [S : mod A B'] [T : mod A B]
[X : func (type_cat I) A] [Y : func (type_cat I) B'] [G : cofunc B' B]
(h : hom X S Y) (t : cotransf_base S Id_cofunc T G) 
[J : Type] [K : func (type_cat J) (type_cat I)]  [L : func (type_cat J) B] (k : hom K (Unit_mod (Y ∘>cb G) Id_func) L) ⊢ eq_refl _ : τ (
((h '∘cb t) ∘>'_(Id_func)) ∘' k =
(h ∘>'_(Id_func) ∘' (cofunc_transp G Y k)) '∘cb t );

//todo: as rule later
type λ [A B' B : cat] [I : Type] [S : mod A B'] [T : mod A B]
[X : func (type_cat I) A] [Y : func (type_cat I) B'] [G : cofunc B' B]
(h : hom X S Y) (t : cotransf_base S Id_cofunc T G) [J] (M : func J A)
[J'] [K : func (type_cat J') J] [L : func (type_cat J') (type_cat I)] (m : hom K (Unit_mod M X) L),
(m '∘ (M)_'∘>  (h '∘cb t)) 
 = (m '∘ (M)_'∘> h) '∘cb  (M 1∘>>cb t);

 symbol cotransf_transp : Π [A' B' A B: cat] [PA' : mod Terminal_cat A'] [PA : mod Terminal_cat A] 
 [R : poly PA' B']  [F : cofunc A' A] [f : cotransf_base PA' Id_cofunc PA F] [S : poly PA B]  [G : cofunc B' B], 
 cotransf R f S G → Π [I : Type]  [Y : func (type_cat I) A']  //conversions uses explicit Terminal_func
 (a : hom (Terminal_func (type_cat I)) PA' Y) (K: func (type_cat I) B'), 
 hom (Elements_intro_func (a '∘cb f)) (poly_mod S) (K ∘>cb G)
 → hom (Elements_intro_func a) (poly_mod R) K;

rule  (@cotransf_transp _ _ _ _ _ _ _ _ _ _ /*explicit $G bcause lost not shared*/ $G $ct _ _ $a $K $s ∘>'_(Id_func) )
       ∘' (@cofunc_transp _ _ $G _ _ _ $X1 $K $x)  
↪ (cotransf_transp $ct ($a ∘↓ $X1) (cofunc_transp_func $G $K $x) ($s ∘>'_(_)  ∘' $x))  ;

assert [A' B' A B: cat] [PA' : mod Terminal_cat A'] [PA : mod Terminal_cat A] 
[R : poly PA' B']  [F : cofunc A' A] [f : cotransf_base PA' Id_cofunc PA F] [S : poly PA B]  [G : cofunc B' B] 
( ct : cotransf R f S G) [I : Type]  [Y : func (type_cat I) A'] 
(a : hom (Terminal_func (type_cat I)) PA' Y) (K: func (type_cat I) B')
(s : hom (Elements_intro_func (a '∘cb f)) (poly_mod S) (K ∘>cb G)) 
I2 (X1: func (type_cat I2) (type_cat I)) (X2: func (type_cat I2) B )
(x : hom X1 (Unit_mod (K ∘>cb G) Id_func) X2 )  ⊢ eq_refl _ : τ (
 (cotransf_transp ct a K s ∘>'_(_) ) ∘' (@cofunc_transp _ _ G _ _ _ X1 K x)  
= (cotransf_transp ct (a ∘↓ X1) (cofunc_transp_func G K x) (s ∘>'_(_)  ∘' x))  );

symbol ''∘c : Π [A' B' A B: cat] [PA' : mod Terminal_cat A'] [PA : mod Terminal_cat A] 
[R : poly PA' B']  [F : cofunc A' A] [f : cotransf_base PA' Id_cofunc PA F] [S : poly PA B]  [G : cofunc B' B]
[A0 B0 : cat] [PA0 : mod Terminal_cat A0]  [F0 : cofunc A A0] [f0 : cotransf_base PA Id_cofunc PA0 F0] [S0 : poly PA0 B0]  [G0 : cofunc B B0],  
cotransf R f S G →  cotransf S f0 S0 G0 → cotransf R (f ''∘cb f0) S0 (G ∘>c G0); 
notation ''∘c infix right 80;

rule cotransf_transp (@''∘c _ _ _ _ _ _ _ _ $f _ $G _ _ _ _ _ _ _  $ct $ct0) $a $K $s 
↪ cotransf_transp $ct $a $K  (cotransf_transp $ct0 ($a '∘cb $f) ($K ∘>cb $G) $s);

assert [A' B' A B: cat] [PA' : mod Terminal_cat A'] [PA : mod Terminal_cat A] 
[R : poly PA' B']  [F : cofunc A' A] [f : cotransf_base PA' Id_cofunc PA F] [S : poly PA B]  [G : cofunc B' B]
[A0 B0 : cat] [PA0 : mod Terminal_cat A0]  [F0 : cofunc A A0] [f0 : cotransf_base PA Id_cofunc PA0 F0] [S0 : poly PA0 B0]  [G0 : cofunc B B0]
(ct : cotransf R f S G) (ct0 : cotransf S f0 S0 G0)
[I : Type]  [Y : func (type_cat I) A'] 
(a : hom (Terminal_func (type_cat I)) PA' Y) (K: func (type_cat I) B')
(s : hom (Elements_intro_func (a '∘cb (f ''∘cb f0))) (poly_mod S0) (K ∘>cb (G ∘>c G0))) ⊢ eq_refl _ : τ (
cotransf_transp (ct ''∘c ct0) a K s 
= cotransf_transp ct a K  (cotransf_transp ct0 (a '∘cb f) (K ∘>cb G) s) );
// : hom (Elements_intro_func a) (poly_mod R) K

/// -------------------------------

// GOAL: cat_poly is substitution-comonoid

constant symbol cat_mod : Π A : cat, mod Terminal_cat A;
constant symbol cat_mod_intro_hom : Π [A : cat] [I : Type] (F : func (type_cat I) A), 
  hom (Terminal_func _) (cat_mod A) F;

rule  @∘' _ _ _ (type_cat _) _ _ _ $Y _ ((cat_mod_intro_hom $F) ∘>'_(Id_func))  $h 
↪ (cat_mod_intro_hom $Y)  ;

assert [A : cat] [I : Type] (F : func (type_cat I) A) [J] [X : func (type_cat J) _] [Y] (h : hom X (Unit_mod F Id_func) Y) ⊢ eq_refl _ : τ (
 (cat_mod_intro_hom F) ∘>'_(Id_func) ∘' h 
 = (cat_mod_intro_hom Y) ) ;

constant symbol cat_poly : Π A : cat, poly (cat_mod A) A;
rule poly_mod (cat_poly $A)
  ↪ Unit_mod (Elements_proj_func (cat_mod $A)) Id_func; 

constant symbol cat_comonoid_base : Π A : cat, cotransf_base (cat_mod A) Id_cofunc ((cat_poly A) ↘poly_base (cat_mod A)) Id_cofunc;
constant symbol cat_comonoid : Π A : cat, cotransf (cat_poly A) (cat_comonoid_base A) ((cat_poly A) ↘poly (cat_poly A)) Id_cofunc; 

rule (cat_mod_intro_hom $F) '∘cb (cat_comonoid_base $A)
↪ Tensor_cov_hom_hom (Elements_intro_func (cat_mod_intro_hom $F))
  (Lambda_cov_transf_hom ((cat_mod_intro_hom $F) ∘>'_(Id_func))) 
  (Func_con_hom (Elements_proj_func (cat_mod $A)) (Elements_intro_func (cat_mod_intro_hom $F)));

assert [A : cat] [I : Type] [F : func (type_cat I) A] ⊢ eq_refl _ : τ (
(cat_mod_intro_hom F) '∘cb (cat_comonoid_base A)
= Tensor_cov_hom_hom (Elements_intro_func (cat_mod_intro_hom F))
    (Lambda_cov_transf_hom ((cat_mod_intro_hom F) ∘>'_(Id_func))) 
    (Func_con_hom (Elements_proj_func (cat_mod A)) (Elements_intro_func (cat_mod_intro_hom F))));
// : hom (Terminal_func (type_cat I)) (cat_poly A ↘poly_base cat_mod A) F

//TODO: REVIEW: IS COMPUTED FORM  OF Elements_intro_func , Elements_proj_func REALLY NECESSARY TO EXPRESS THE LHS OF THIS RULE?
// SEE BELOW: OTHERWISE SUBSEQUENT TEST ASSERTION ON SAME EXPRESSION FAILS (BECAUSE THEY Elements_intro_func , Elements_proj_func ARE INNER SYMBOLS WHICH ARE REDUCED FIRST)
rule cotransf_transp (cat_comonoid $A) (cat_mod_intro_hom $F) $K (↘poly_intro_hom (cat_poly $A) (cat_poly $A) (Lambda_cov_transf_hom (cat_mod_intro_hom $F ∘>'_ Id_func)) (Func_con_hom (Context_elimCat_func (Comma_cov_catd (Terminal_catd Terminal_cat) (cat_mod $A))) (Context_intro_func (Comma_cov_intro_funcd (Terminal_catd Terminal_cat) (cat_mod_intro_hom $F)))) $r' $s')
↪ (Func_con_hom (Elements_proj_func (cat_mod $A)) (Elements_intro_func (cat_mod_intro_hom $F))) ∘>'_(_) ∘' ($r' ∘>'_(_) ∘' $s');

assert  [A : cat] [I : Type] [F : func (type_cat I) A] [K: func (type_cat I) A] [H : func (type_cat I) A] (r': hom Id_func (Elements_intro_func (cat_mod_intro_hom F) ∘>> poly_mod (cat_poly A)) H) 
(s' : hom Id_func ((Elements_intro_func (Eval_cov_hom_transf (Lambda_cov_transf_hom (cat_mod_intro_hom F ∘>'_ Id_func)) ∘' r')) ∘>> (poly_mod (cat_poly A))) K ) ⊢ 
cotransf_transp (cat_comonoid A) (cat_mod_intro_hom F) K
  (↘poly_intro_hom (cat_poly A) (cat_poly A) 
      (Lambda_cov_transf_hom ((cat_mod_intro_hom F) ∘>'_(Id_func))) 
      (Func_con_hom (Elements_proj_func (cat_mod A)) (Elements_intro_func (cat_mod_intro_hom F)))
      r' s') 
≡  (Func_con_hom (Elements_proj_func (cat_mod A)) (Elements_intro_func (cat_mod_intro_hom F))) ∘>'_(_) ∘' (r' ∘>'_(_) ∘' s');
// : hom (Elements_intro_func (cat_mod_intro_hom F)) (poly_mod (cat_poly A)) K

//TODO: REVIEW:  FAILING (SLOW) ORIGINAL ATTEMPT AT ABOVE RULE.
// would be stuck slow without opaque command;
// and regardless it register a useless rule whose identical assertion fails 
opaque Elements_cat; opaque Elements_intro_func;
opaque Elements_proj_func; opaque Elements_intro_hom;
assert [B I : cat] [R : mod Terminal_cat B] [y : func I B] (r : hom (Terminal_func I) R y) ⊢
@Elements_intro_func B I R y r ∘> Elements_proj_func R ≡ y;

rule cotransf_transp (cat_comonoid $A) (cat_mod_intro_hom $F) $K
  (↘poly_intro_hom (cat_poly $A) (cat_poly $A) 
    (Lambda_cov_transf_hom ((cat_mod_intro_hom $F) ∘>'_(Id_func))) 
    (Func_con_hom (Elements_proj_func (cat_mod $A)) (Elements_intro_func (cat_mod_intro_hom $F)))
    $r' $s') 
↪ (Func_con_hom (Elements_proj_func (cat_mod $A)) (Elements_intro_func (cat_mod_intro_hom $F))) ∘>'_(_) ∘' ($r' ∘>'_(_) ∘' $s');


/* voila */
