/* https://github.com/1337777/cartier/blob/master/cartierSolution16.lp 
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

https://github.com/1337777/cartier/blob/master/Kosta_Dosen_2pages.pdf

OUTLINE OF cartierSolution16.lp :

# SIEVES
## SIEVES CLASSIFIER
## OPERATIONS ON SIEVES

# SITES
## SHEAFIFICATION AND GLUE
## CLOSED-SIEVES CLASSIFIER, CLOSURE OPERATION
## SUB-SHEAVES
## OPERATIONS ON CLOSED SIEVES

# SCHEMES
## RING ALGEBRA INTERFACE
## LOCALIZATION OF RINGS
## PROFUNCTORS/PRESHEAVES OF RINGS
## LOCALLY RINGED SITES
## SLICE SITE, CONTINUOUS SITE MORPHISM WITH CONTINUOUS RIGHT ADJOINT
## AFFINE SCHEME INTERFACE: PART 1, SLICE OF AFFINE SCHEME IS AFFINE
## SCHEME INTERFACE, AFFINE COVER
## AFFINE SCHEME INTERFACE: PART 2, INTERFACE FOR JOIN COVER BY BASIC OPENS
## AFFINE SCHEME INTERFACE: PART 3, INTERFACE FOR UNIMODULAR COVER OF A BASIC OPEN

# COMMENTS


GOTO cartierSolution13.lp FOR:

# CONTEXT EXTENSION
## CONTEXT EXTENSION FOR CATEGORIES

# SIGMA-SUM: PART 1
## SIGMA-SUM FOR CATEGORIES

# PI-PRODUCT: PART 1
## PI-PRODUCT FOR CATEGORIES

# CONTEXT EXTENSION
## CONTEXT EXTENSION FOR PROFUNCTORS

# SIGMA-SUM: PART 2
## SIGMA-SUM OF PROFUNCTORS

# PI-PRODUCT: PART 2
## FULLY GENERAL SIGMA/PI CONSTRUCTIONS ON FIBRED PROFUNCTORS

*/

require open modos.cartierSolution13;

verbose 10; 
flag "print_contexts" on; flag "print_domains" on; flag "print_meta_types" on; 
// flag "print_implicits" on; 
// debug +a; //debug +acdeghiklmoprsyuvxyz;
print coerce_rule; // /!\ BUG, DONT USE, ONLY CONSOLE print unif_rule;
// search "spine = (cartierSolution13.cat → cartierSolution13.cat) , hyp = cartierSolution13.cat";


/*****************************************
* # SIEVES
* ## SIEVES CLASSIFIER
******************************************/

// Subprofunctor classifier

/* I could be a site too... then collection of classifiers is locally constant */
constant symbol sieve : Π (S : cat) (I : cat), mod S I;

// classifier over Unit_mod ... required? together with classifier subclassifier_modd over any mod context
injective symbol sieve_modd : Π [S : cat] [I] [F : func I S] [D] [K : func I D], Π (ff : hom F (sieve S D) K), 
modd (Terminal_catd _) (Unit_mod Id_func F) (Terminal_catd _);

injective symbol sieve_mod  [S : cat] [I] [F : func I S] [D] [K : func I D] (ff : hom F (sieve S D) K) 
: mod S I ≔ Context_mod (sieve_modd ff);

injective symbol sieve_mod_proj_transf  [A : cat]  [I] [F : func I A] 
[D] [K : func I D] (ff : hom F (sieve A D) K)
: transf (sieve_mod ff) Id_func (Unit_mod Id_func F) Id_func
≔ Context_elimMod_transf (sieve_modd ff);

// pullback of sieve, defined symbol, could eventually compute to concrete sieve
symbol pullback_sieve  [S : cat] [I] [F : func I S] [D] [K : func I D]
(ff : hom F (sieve S D) K) [J] [G : func J S] [x : func J I] (g : hom G (Unit_mod Id_func F) x)
:  hom G (sieve S D) (x ∘> K)
≔ (g '∘ (_)_'∘> ff);

rule Fibre_modd (sieve_modd $ff) ((Id_func)_'∘> $g)
↪ sieve_modd (pullback_sieve $ff $g);

// classifier subclassifier_modd over any mod context
injective symbol subclassifier_modd : Π [S : cat]  
[I ] [E : mod S I] [D] [K : func I D], Π (ff : transf E Id_func (sieve S D) K), 
modd (Terminal_catd S) E (Terminal_catd I) ;

injective symbol subclassifier_modd_intro_transfd : Π [S : cat]  
[I ] [E : mod S I ]  [D] [K : func I D], Π (ff : transf E Id_func (sieve S D) K)
[J] [G  : func J S] [i : func J I] (e : hom G E i ),
// this uses classifier sieve_modd over Unit_mod 
transfd ((_)_'∘> e) (sieve_modd (e '∘ ff)) Id_funcd (subclassifier_modd ff) (Terminal_funcd _ _ ); 

injective symbol subclassifier_modd_intro_transf  [S : cat]  
[I ] [E : mod S I ]  [D] [K : func I D] (ff : transf E Id_func (sieve S D) K)
[J] [G  : func J S] [i : func J I] (e : hom G E i )
: transf (sieve_mod (e '∘ ff)) Id_func (Context_mod (subclassifier_modd ff)) i 
≔ Context_intro_transf (subclassifier_modd_intro_transfd ff e) ; 

rule @Fibre_modd _ _ _ _ _ _ _ (subclassifier_modd $ff) _ Id_func _ ($t)
↪ (subclassifier_modd ($t ''∘ $ff));

// shortcuts, not necessary
rule subclassifier_modd ((Id_func)_'∘> $ff)
↪ sieve_modd $ff;
rule subclassifier_modd_intro_transfd ((Id_func)_'∘> $ff) $e
↪ Fibre_elim_transfd (sieve_modd $ff) ((Id_func)_'∘> $e) ;


// --------------------------------------------
// # SIEVES
// ## OPERATIONS ON SIEVES


// subobject, predicatess version

constant symbol sub_mod : Π [S : cat]  
[I ] [E : mod S I /* ≔ Unit_mod Id_func F */ ]  [D] [K : func I D], Π (ff : transf E Id_func (sieve S D) K), 
mod S I;

// some form of adjunction transpose
constant symbol sub_mod_intro_transf : Π [S : cat]  
[I ] [E : mod S I ]  [D] [K : func I D], Π (ff : transf E Id_func (sieve S D) K)
[J] [G  : func J S] [i : func J I] (e : hom G E i ),
transf (sieve_mod (e '∘ ff)) Id_func (sub_mod ff) i; 

// maximal sieve

constant  symbol maximal_sieve : Π [S : cat] [I] (F : func I S) [D] (K : func I D), hom F (sieve S D) K;

//note that extra argument $K is ignored
rule sieve_modd (maximal_sieve $F $K)
↪ Terminal_modd (Unit_mod Id_func $F)  ;

//convenient shortcut, not neccessary; moreover this reduction already happens via another rule on Context_mod Terminal_modd
// rule Context_mod (sieve_modd (maximal_sieve $F $K))
// ↪ (Unit_mod Id_func $F)  ;

injective symbol maximal_sieve_intro_transf [S : cat] [I] (F : func I S) [D] (K : func I D)
: transf (Unit_mod Id_func F) Id_func (sieve_mod (maximal_sieve F K)) Id_func
≔ Context_intro_transf /*( (Id_func) _'∘> (Func_cov_hom F Id_func) ) */(Terminal_transfd (Terminal_modd (Unit_mod Id_func F)) ( (Id_func) _'∘> (Func_cov_hom F Id_func) ));

// intersection sieve

// REVIEW: intersection is similar as ("non-dependent") instance of sub/sum (of pullbacks of single sieve) along another sieve;
// but the sieve-clasure (which is only left-exact) would be different?
constant symbol intersection_sieve : Π [S : cat] [I] [F : func I S] [D] [K : func I D]
(ff ff' : hom F (sieve S D) K /* need not share same K... when sum form */), hom F (sieve S D) K; 

rule sieve_modd (intersection_sieve $ff $ff')
↪ product_modd (sieve_modd $ff) (sieve_modd $ff');

// subsieve

constant symbol sub_sieve : Π [S : cat] [I] [F : func I S] [D] [K : func I D], 
Π (ff : hom F (sieve S D) K) [D'] [H : func I D'], 
transf (sieve_mod ff) Id_func (sieve S D') H
→ hom F (sieve S D') H;

rule (sieve_modd (sub_sieve $ff $T_))
↪ Sigma_modd (sieve_modd $ff) (subclassifier_modd $T_);

symbol sub_sieve_intro_transf [S : cat] [I] [F : func I S][D] [K : func I D] 
(ff : hom F (sieve S D) K) [D'] [H : func I D'] (T_ : transf (sieve_mod ff) Id_func (sieve S D') H)
[J] [G : func J S] [f_i: func J I] (f : hom G (sieve_mod ff) f_i)
: transf (sieve_mod (f '∘ T_)) Id_func (sieve_mod (sub_sieve ff T_)) f_i
≔ Context_intro_transf
(subclassifier_modd_intro_transfd  T_ f 
''∘d Sigma_intro_transfd (sieve_modd ff) (subclassifier_modd T_));

/// alternative definition of intersection sieve (positive/negative form ... similar as primitive product vs inductive sum... so both ok)
// but the sieve-clasure (which is only left-exact) would be different?
symbol intersection_as_sub_sieve_of_pullbacking [S : cat] [I] [F : func I S] 
[D] [K : func I D] (ff : hom F (sieve S D) K) 
[D'] [H : func I D'] (T_ : hom F (sieve S D') H) : hom F (sieve S D') (   H)
 ≔ sub_sieve ff (sieve_mod_proj_transf ff ''∘ ((_) _'∘> T_)) ;


// --------------------------------------------
// # SITES
// ## SHEAFIFICATION AND GLUE


constant symbol site : cat → TYPE ; 
constant symbol site_type : cat → Type;
rule τ (site_type $C) ↪ site $C;

// classifier for sheaves, not internalized

constant symbol smod : Π [S : cat] (S_site : site S) (I : cat), TYPE ;
constant symbol smod_type : Π [S : cat] (S_site : site S) (I : cat), Type ;
rule τ (@smod_type $S $A $B) ↪ @smod $S $A $B;

injective symbol smod_mod : Π [S : cat] [S_site : site S] [I : cat], smod S_site I → mod S I ;

// sheafification

symbol mod_smod : Π [S : cat] (S_site : site S) [I : cat], mod S I → smod S_site I ;

rule (mod_smod $S_site (@smod_mod _ $S_site _ $R)) ↪ $R;

// glue (extension)

constant symbol glue  [A B : cat] (A_site : site A)  (R : smod A_site B) [I] [G : func I B] 
(L : mod A I)
(r_ : transf L Id_func (smod_mod R) G)
: transf (smod_mod (mod_smod A_site L)) Id_func (smod_mod R) G;

// unit of sheafification
injective symbol eta_smod_transf : Π [S : cat] (S_site : site S) [I : cat] (R : mod S I),
Π [J] [x : func J _] [y : func J _],
hom x R y → hom x (smod_mod (mod_smod S_site R)) y ;

//REVIEW: this transf version of eta has a problem with rewrite rules
// constant symbol eta_smod_transf' : Π [S : cat] (S_site : site S) [I : cat] (R : mod S I),
//    transf R Id_func (smod_mod (mod_smod S_site R)) Id_func ;

rule ( (eta_smod_transf $A_site $L $x)) '∘ (glue  $A_site _ $L $rr)
↪ $x '∘ $rr;


// --------------------------------------------
// # SITES
// ## CLOSED-SIEVES CLASSIFIER, CLOSURE OPERATION


// classifier for closed sieves, internalized
/// does anything gained from viewing it as a smod of sieve?
constant symbol ssieve [S : cat] (S_site : site S) (I : cat) : smod S_site I;

// closure/sheafification operation on any sieve; here the eta of sheafification is onlt the separation step
constant symbol sieve_ssieve [S : cat] (S_site : site S) (I : cat):
 transf (sieve S I) Id_func (smod_mod (ssieve S_site I)) Id_func ;

// the transf alternative version seems to have problems in the rewrite rules where application '∘ is nested
injective symbol ssieve_sieve : Π [S : cat] (S_site : site S) [I : cat],
Π [J] [F : func J S] [K], hom F (smod_mod (ssieve S_site I))  K → hom F (sieve S I) K;
// extra operation with context necessary because no the transf version
constant  symbol ssieve_sieve_ctx : Π [S : cat] (S_site : site S) [I : cat],
//todo allow I to vary
Π [J] [E : mod S J] [K], transf E Id_func (smod_mod (ssieve S_site I)) K → transf E Id_func (sieve S I) K;
rule  $e '∘ (ssieve_sieve_ctx $S_site $T_)
↪ (ssieve_sieve $S_site ($e '∘ $T_));

rule (ssieve_sieve $S_site $ff) '∘ sieve_ssieve $S_site _ ↪  $ff;

//TODO: REDO THIS WITH A NEW smodd (dependent sheaves)
injective symbol ssieve_smod : Π [S : cat] (S_site : site S)  [I] [F : func I S] [D] [K : func I D], Π (ff : hom F (smod_mod (ssieve S_site D)) K),
smod S_site I;

// sheafification is compatible with sieve-closure operation
rule mod_smod $S_site (Context_mod (sieve_modd $ff)) 
  ↪ (ssieve_smod $S_site (($ff '∘ (sieve_ssieve $S_site _))));

rule (smod_mod (ssieve_smod $S_site $ff))
 ↪ (sieve_mod (ssieve_sieve $S_site $ff));

// alternative defined consequences of glue
symbol glue_sieve_mod_def  [A B : cat] (A_site : site A) [I] [F : func I A]  (R : smod A_site B)  [G : func I B] [D] [K : func I D] (ff : hom F (sieve A D) K)
(rr : transf (sieve_mod ff) Id_func (smod_mod R) G) :
 transf (smod_mod (ssieve_smod A_site ((ff '∘ (sieve_ssieve A_site _))))) Id_func (smod_mod R) G 
 ≔ glue A_site R (sieve_mod ff) rr;

// alternative defined consequences of glue
symbol glue_sieve_mod_endo_def  [A B : cat] (A_site : site A) [I] [F : func I A]  (R : smod A_site B)  [G : func I B] [D] [K : func I D] (ff : hom F (sieve A D) K)
(rr : transf (sieve_mod ff) Id_func (smod_mod R) G)
: transf (sieve_mod (ssieve_sieve A_site (ff '∘ (sieve_ssieve A_site D)))) Id_func (smod_mod R) G
≔  glue_sieve_mod_def A_site R ff rr ;

// alternative defined consequences of glue
symbol glue_sieve_mod_closed_def  [A  : cat] [A_site : site A] [I] [F : func I A]  [D] [K : func I D] [ff : hom F (sieve A D) K] [J] [G : func J A] [D'] [K' : func J D'] [gg : hom G (smod_mod (ssieve A_site D')) K'] [H : func I J]
(t_ : transf (sieve_mod ff) Id_func (smod_mod (ssieve_smod A_site gg)) H)
: transf (smod_mod (ssieve_smod A_site ((ff '∘ (sieve_ssieve A_site _))))) Id_func (smod_mod (ssieve_smod A_site gg)) H
≔ glue A_site (ssieve_smod A_site gg) (sieve_mod ff) t_;

 
// --------------------------------------------
// # SITES
// ## SUB-SHEAVES


//TODO: redo via fibred sheafprofuctors?
constant symbol sub_smod : Π [S : cat] (S_site : site S) 
[I ] [E : smod S_site I ] /* ?not necessarily smod base */ [D] [K : func I D], 
Π (ff : transf (smod_mod E) Id_func (smod_mod (ssieve S_site D)) K), 
smod S_site I ;

constant symbol sub_smod_intro_transf : Π [S : cat]  (S_site : site S) 
[I ] [E : smod S_site I /* ≔ Unit_mod Id_func F */ ]  [D] [K : func I D], Π (ff : transf (smod_mod E) /* understood E is already smod */ Id_func (smod_mod (ssieve S_site D)) K)
[J] [G  : func J S] [i : func J I] (e : hom G (smod_mod E) i ),
transf (smod_mod (ssieve_smod S_site (e  '∘ (/* glue S_site E */ ff) ))) Id_func (smod_mod (sub_smod S_site ff)) i; 

// sheafification of sigma/sum/sub is always non-trivial (does not just commute)
rule mod_smod $S_site (sub_mod $ff_) 
↪ (sub_smod $S_site ( glue $S_site (ssieve $S_site _) _ ($ff_ ''∘ (sieve_ssieve $S_site _))));

//REVIEW: could use eta instead?
rule (smod_mod (sub_smod $S_site $ff))
↪ (sub_mod (ssieve_sieve_ctx $S_site $ff));

// alternative defined consequences of glue
symbol glue_sieve_mod_ctx [A B : cat] (A_site : site A) [I]  (R : smod A_site B)  [G : func I B] [E : mod A I ]  [D] [K : func I D] (ff : transf E Id_func (sieve A D) K)
(rr : transf (sub_mod ff) Id_func (smod_mod R) G)
: transf (smod_mod (sub_smod A_site (glue A_site (ssieve A_site D) E (ff ''∘ (sieve_ssieve A_site D)) ))) Id_func (smod_mod R) G
 ≔ glue A_site R (sub_mod ff) rr;

// alternative defined consequences of glue
symbol glue_sieve_mod_ctx_endo [A B : cat] (A_site : site A) [I]   (R : smod A_site B)  [G : func I B] [E : mod A I  ]  [D] [K : func I D] (ff : transf E Id_func (sieve A D) K)
(rr : transf (sub_mod ff) Id_func (smod_mod R) G)
: transf (sub_mod ((ssieve_sieve_ctx A_site (glue A_site (ssieve A_site D) E (ff ''∘ (sieve_ssieve A_site D)) )) )) Id_func (smod_mod R) G
≔ glue_sieve_mod_ctx A_site R ff rr;


rule ($x '∘ ((sub_smod_intro_transf $A_site ( _ /* DON'T SPECIFY THIS (glue $A_site _ $E ($ff ''∘ sieve_ssieve $A_site $D)) */)  (eta_smod_transf $A_site $E $e) ))) 
  '∘  (glue $A_site $R (@sub_mod  _ _ $E _ _  $ff) $rr)
↪  $x '∘ (glue $A_site $R (sieve_mod ($e '∘ $ff)) ((sub_mod_intro_transf $ff $e) ''∘ $rr));

assert [A B : cat] [A_site : site A] [I]   [R : smod A_site B]  [G : func I B] [E : mod A I]  [D] [K : func I D] (ff : transf E Id_func (sieve A D) K)
(rr : transf (sub_mod ff) Id_func (smod_mod R) G) [J] (e_X: func J A) (e_Y: func J I) (e: hom e_X E e_Y) 
[J'] [X : func J' _] [Y : func J' _] (x : hom X (smod_mod (mod_smod A_site (sieve_mod (e '∘ ff)))) Y) ⊢
(x '∘ ((sub_smod_intro_transf A_site (  ( (/* DON'T SPECIFY THIS IN RULE */ (glue A_site (ssieve A_site _) E (ff ''∘ sieve_ssieve A_site D)))) ) (eta_smod_transf A_site E e)))) '∘  (glue A_site R (@sub_mod  _ _ E _ _  ff) rr)
≡ x '∘ (glue A_site R (sieve_mod (e '∘ ff)) ((sub_mod_intro_transf ff e) ''∘ rr));

 
// --------------------------------------------
// # SITES
// ## OPERATIONS ON CLOSED SIEVES

// maximal closed sieve

// no intro rules, just a rule to compute the underlying sieve where intros happen
constant  symbol maximal_ssieve : Π [S : cat] (S_site : site S) [I] (F : func I S) [D] (K : func I D), hom F (smod_mod (ssieve S_site D)) K;

rule ((maximal_sieve $F $K) '∘ (sieve_ssieve $S_site $D))
↪ (maximal_ssieve $S_site $F $K);

rule (ssieve_sieve _ (maximal_ssieve $S_site $F $K))  
↪ (maximal_sieve $F $K); 

//TODO REDO THIS USING smodd (dependent sheaves)
rule (ssieve_smod $S_site (maximal_ssieve $S_site $F $K))  
↪ mod_smod $S_site (Unit_mod Id_func $F);

// intersection closed sieve

constant symbol intersection_ssieve : Π [S : cat] (S_site : site S) [I] [F : func I S] [D] [K : func I D]
// would not need to share same K... if the sub_sieve formulation was used
(ff ff' : hom F (smod_mod (ssieve S_site D)) K), hom F (smod_mod (ssieve S_site D)) K; 

//TODO: also declare the corresponding eta (which would be inverse in the explicit morphism formulation) as identity
rule ((intersection_sieve $ff $ff') '∘ (sieve_ssieve $S_site $I)) 
↪ (intersection_ssieve $S_site (($ff '∘ (sieve_ssieve $S_site $I))) (($ff' '∘ (sieve_ssieve $S_site $I)) )); 

// there was confluence problem before; alternative would be via isos reverse to eta share between sieve and mod
rule (ssieve_sieve $S_site (intersection_ssieve $S_site $ff $ff'))
↪  (intersection_sieve (ssieve_sieve $S_site $ff) (ssieve_sieve $S_site $ff')) ; 

// sub-sieve of closed sieve by closed predicate

constant symbol sub_ssieve : Π [S : cat] (S_site : site S) [I] [F : func I S] [D] [K : func I D], 
Π (ff : hom F (smod_mod (ssieve S_site D)) K) [D'] [H : func I D'], 
transf (smod_mod (ssieve_smod S_site ff)) Id_func (smod_mod (ssieve S_site D')) H
→ hom F (smod_mod (ssieve S_site D')) (   H);

// non-trivial sheafification as expected of sigma/sum/sub
rule (sub_sieve $ff $gg_ ) '∘ (sieve_ssieve $S_site _)
↪ (sub_ssieve $S_site _ ( glue $S_site _ _ ($gg_ ''∘ (sieve_ssieve $S_site _))));

/// as morphism too but not iso because extra glue, when precomp with eta gives functorial sub_sieve
rule (ssieve_sieve $S_site (sub_ssieve $S_site $ff $gg_))
↪ (sub_sieve (ssieve_sieve $S_site $ff) (ssieve_sieve_ctx $S_site $gg_));


// --------------------------------------------
// # SCHEMES
// ## RING ALGEBRA INTERFACE


// rings 
constant symbol ring : Type → TYPE ; 
symbol ring_type [R_type : Type] (R : ring R_type) : TYPE ≔ τ R_type;

symbol ring_one : Π [R_type : Type] (R : ring R_type), ring_type R;
symbol ring_mult : Π [R_type : Type] (R : ring R_type) (r s : ring_type R), ring_type R;
symbol ring_inv [R_type : Type] (R : ring R_type) (r : ring_type R): TYPE 
 ≔ τΣ_ (λ r_inv, ring_mult R r r_inv = ring_one R);

// role appear only later, for unimodular sieve
symbol ring_add : Π [R_type : Type] (R : ring R_type) (r s : ring_type R), ring_type R;

// morphisms of rings
constant symbol ring_morph : Π [R_type : Type] (R : ring R_type) [T_type : Type] (T : ring T_type), TYPE;
constant symbol ring_morph_type : Π [R_type : Type] (R : ring R_type) [T_type : Type] (T : ring T_type), Type;
rule τ (ring_morph_type $R $T) ↪ ring_morph $R $T;

symbol ring_morph_fun : Π [R_type : Type] [R : ring R_type] [T_type : Type] [T : ring T_type], ring_morph R T → ring_type R → ring_type T;

// some very minimal preliminary details of algebra

// inductive nat : TYPE ≔  .. natural numbers defined in another file 
//REVIEW: QUESTION: must use actual compuations or only the logical interface of nat numbers?
symbol + : nat → nat → nat; notation + infix left 20;
rule 0 + $y ↪ $y
with ($x +1) + $y ↪ ($x + $y) +1 ;

constant symbol ring_eq_mult_oneR : Π [R_type : Type] (R : ring R_type), Π (f : ring_type R),
  τ (ring_mult R f (ring_one R) = f);
constant symbol ring_eq_mult_oneL : Π [R_type : Type] (R : ring R_type), Π (f : ring_type R),
  τ (ring_mult R (ring_one R) f = f);

// defined symbol, not part of the structure
symbol ring_exp : Π [R_type : Type] (R : ring R_type) (r : ring_type R) (n : nat), ring_type R;
rule ring_exp $R $r ($n +1) ↪ ring_mult $R (ring_exp $R $r $n) $r
with ring_exp $R $r 0 ↪ ring_one $R;


// --------------------------------------------
// # SCHEMES
// ## LOCALIZATION OF RINGS


// interface for localization of rings

constant symbol ring_loc : Π [R_type : Type] (R : ring R_type) (f : ring_type R) [Rf_type : Type] (Rf : ring Rf_type), TYPE;

constant symbol ring_loc_intro : Π [R_type : Type] [R : ring R_type] [f : ring_type R] [Rf_type : Type] [Rf : ring Rf_type], ring_loc R f Rf → 
ring_type R →  nat → ring_type Rf;

constant symbol ring_loc_intro_rel : Π [R_type : Type] [R : ring R_type] [f : ring_type R] [Rf_type : Type] [Rf : ring Rf_type] (Rf_ring_loc : ring_loc R f Rf), 
Π (r : ring_type R) (n : nat) (s : ring_type R) (m : nat) (k : nat), 
τ ( ring_mult R (ring_exp R f k) (ring_mult R (ring_exp R f m) r) 
   = ring_mult R (ring_exp R f k) (ring_mult R (ring_exp R f n) s)) → 
τ (ring_loc_intro Rf_ring_loc r n = ring_loc_intro Rf_ring_loc s m);

// ?should skip inductive-set elimination and go directly to univ algebra? and should be univ formulation for rings or for  R-algebras?
constant symbol ring_loc_elim : Π [R_type : Type] [R : ring R_type] [f : ring_type R] [Rf_type : Type] [Rf : ring Rf_type], ring_loc R f Rf → 
Π [T_type : Type] [T :  ring T_type],
/* ring map (by the way making T into R-alg), not present when univ for R-algebras */
Π (m :  ring_morph R T),
// witness that f is indeed invertible
ring_inv T (ring_morph_fun m f) 
→ ring_morph Rf T;

// computation rules for both hypothesis: when input is (r,0) = r/f^0 ; when input is (1, 1) = 1/f^1
rule ring_morph_fun (ring_loc_elim $Rf_loc $m $mf_inv) (ring_loc_intro $Rf_loc $r 0)
↪ ring_morph_fun $m $r;
rule ring_morph_fun (ring_loc_elim $Rf_loc $m $mf_inv) (@ring_loc_intro _ $R _ _ _ $Rf_loc (ring_one $R) 1)
↪ sigma_Fst $mf_inv;

// rest of the interface specification

constant symbol ring_loc_ring_mult: Π [R_type : Type] [R : ring R_type] [f : ring_type R] [Rf_type : Type] [Rf : ring Rf_type] (Rf_loc : ring_loc R f Rf),
Π (r : ring_type R) (n : nat) (s : ring_type R) (m : nat),
τ (ring_mult Rf (ring_loc_intro Rf_loc r n) (ring_loc_intro Rf_loc s m) 
  = (ring_loc_intro Rf_loc (ring_mult R r s) (n + m)));

constant symbol ring_loc_ring_one: Π [R_type : Type] [R : ring R_type] [f : ring_type R] [Rf_type : Type] [Rf : ring Rf_type] (Rf_loc : ring_loc R f Rf),
τ (ring_one Rf = (ring_loc_intro Rf_loc (ring_one R) 0));

// sanity check
// derived proof that the ring element f becomes indeed invertible in the localization away from f
opaque symbol ring_loc_ring_inv [R_type : Type] [R : ring R_type] [f : ring_type R] [Rf_type : Type] [Rf : ring Rf_type] (Rf_loc : ring_loc R f Rf) (v : τ (ring_mult Rf (ring_loc_intro Rf_loc f 0) (ring_loc_intro Rf_loc (ring_one R) 1) = ring_one Rf) ) 
: ring_inv Rf (ring_loc_intro Rf_loc f 0) ≔
begin
  assume R_type R f Rf_type Rf Rf_loc v;
  refine (Struct_sigma (ring_loc_intro Rf_loc (ring_one R) 1) _);
  rewrite (ring_loc_ring_mult Rf_loc); simplify;
  rewrite ring_eq_mult_oneR R; rewrite ring_loc_ring_one Rf_loc;
  apply ring_loc_intro_rel Rf_loc _ _ _ _ 0; simplify;
  rewrite ring_eq_mult_oneL R; rewrite ring_eq_mult_oneL R; rewrite ring_eq_mult_oneL R;
  rewrite ring_eq_mult_oneR R; reflexivity;
end;



// --------------------------------------------
// # SCHEMES
// ## PROFUNCTORS/PRESHEAVES OF RINGS

 
constant symbol mod_ring : Π [A B : cat]  (M : mod A B), TYPE ;
constant symbol mod_ring_type : Π [A B : cat] (M : mod A B), Type ;
rule τ (mod_ring_type $M) ↪ mod_ring $M;


symbol mod_ring_ring : Π [A B A' : cat] [I] (U : func I A') (F : func A' A) [M_mod : mod A B] (M : mod_ring M_mod) (G : func I B), ring (hom_type U (F ∘>> M_mod) G);

symbol mod_ring_con_ring_morph : Π [A B A' : cat] [I] [U : func I A']  
[V : func I A'] (v : hom V (Unit_mod Id_func /* H ? */ U) Id_func /* x */ ) (F : func A' A) [M_mod : mod A B] (M : mod_ring M_mod) (G : func I B), ring_morph (mod_ring_ring U F M G) (mod_ring_ring V F M G) ;

rule ring_morph_fun (mod_ring_con_ring_morph $v $F $M $G) $m 
↪  $v '∘ (_)_'∘> $m ;

//TODO: ALSO FOR ∘>>_intro
symbol mod_ring_pullb_proj_ring_morph : Π [A B A' A'' : cat] [I] (U : func I A'') (F' : func A'' A') (F : func A' A) [M_mod : mod A B] (M : mod_ring M_mod) (G : func I B),
 ring_morph (mod_ring_ring U (F' ∘> F) M G) (mod_ring_ring (U ∘> F') F M G) ;

rule ring_morph_fun (@mod_ring_pullb_proj_ring_morph _ _ _ _ _ $U $F' $F $M_mod $M $G) $m 
↪ ( ∘>>_proj $F' ($F ∘>> $M_mod) ) ∘' $m ;

constant symbol mod_pullb_mod_ring : Π [A B : cat] [M_mod : mod A B], mod_ring M_mod → Π [A' : cat] (F : func A' A), mod_ring (F ∘>> M_mod);

rule mod_ring_ring $V $F' (mod_pullb_mod_ring $M $F ) $G
↪ mod_ring_ring $V ($F' ∘> $F) $M $G;
rule mod_ring_con_ring_morph $v $F' (mod_pullb_mod_ring $M  $F) $G
↪ mod_ring_con_ring_morph $v ($F' ∘> $F) $M $G;
rule mod_ring_pullb_proj_ring_morph $U $F'' $F' (mod_pullb_mod_ring $M  $F) $G
↪ mod_ring_pullb_proj_ring_morph $U $F'' ($F' ∘> $F) $M $G;

//THIS ATTEMPT DONT WORK... ISOS ARE REQUIRED
// constant symbol mod_pullb_mod_ring : Π [A B : cat] [I] (U : func I A) [M_mod : mod A B] (M : mod_ring M_mod), mod_ring (U ∘>> M_mod);
// rule mod_ring_ring $V (mod_pullb_mod_ring $U $M) $G
// ↪ mod_ring_ring ($V ∘> $U) $M $G;



// --------------------------------------------
// # SCHEMES
// ## LOCALLY RINGED SITES


constant symbol mod_loc : Π [S : cat] [O : mod S Terminal_cat] (O_ring : mod_ring O), TYPE;

// invertibility support sieve a.k.a D(-)
symbol mod_loc_sieve : Π [S : cat] [O : mod S Terminal_cat] [O_ring : mod_ring O],
mod_loc O_ring →
Π [S'] (F : func S' S) [I] [U : func I S'] (f : hom U (F ∘>> O) (Terminal_func _)), 
hom U (sieve S' Terminal_cat) (Terminal_func _);

symbol mod_loc_sieve_intro_hom : Π [S : cat] [O : mod S Terminal_cat] [O_ring : mod_ring O] (D : mod_loc O_ring),
Π [S'] (F : func S' S) [I] [U : func I S'] (f : hom U (F ∘>> O) (Terminal_func _)), 
//TODO: generalize here: hom V (Unit_mod Id_func U) x
Π [V : func I S'] (v : hom V (Unit_mod Id_func U) Id_func /*TODO: gen x */) (f_inv : ring_inv (mod_ring_ring V F O_ring (Terminal_func _)) (v '∘ (_)_'∘> f )),
hom V (sieve_mod (mod_loc_sieve D F f)) Id_func;
//?todo: add that projection to underlying arrow is inv ?

// analogue of Vakil's qcqs-sheme lemma:
//  ( compat family = ) lim_V_a (O_X(V_a : DD(f))) =  O_X(U)[1/f]    
symbol mod_loc_elim : Π [S : cat] [O : mod S Terminal_cat] [O_ring : mod_ring O] (D : mod_loc O_ring),
Π [S'] (F : func S' S) [I] [U : func I S'] (f : hom U (F ∘>> O) (Terminal_func _)), 
Π [OU_f_type : Type] [OU_f : ring OU_f_type] (Of_loc : ring_loc (mod_ring_ring U F O_ring (Terminal_func _)) f OU_f),
// 1. TODO: ?should be ring morphisms? how? make transf a ring when target is a mod_ring
// 2. ?should instead generalize to any target where f is inv?
transf (sieve_mod (mod_loc_sieve D F f)) Id_func (F ∘>> O) (Terminal_func _)
 → ring_type OU_f; 

//TODO: when mod_loc_elim is given as input to mod_loc-extensions of restriction maps then the output is the corresponding componet of mod_loc_elim transf

//generalize those Id_func ?
rule ring_morph_fun (ring_loc_elim $Of_loc (mod_ring_con_ring_morph $v $F $O_ring $Id_func) $f_inv) (@mod_loc_elim _ _ $O_ring $D _ $F _ _ $f _ _ $Of_loc $g_ )
↪ (mod_loc_sieve_intro_hom $D $F $f $v $f_inv) '∘ $g_ ; 

assert [S : cat] [O : mod S Terminal_cat]  [O_ring : mod_ring O] (D : mod_loc O_ring) [S'] (F : func S' S) [U : func Terminal_cat S'] (f : hom U (F ∘>> O) Id_func) [OU_f_type : Type] [OU_f : ring OU_f_type] (Of_loc : ring_loc (mod_ring_ring U F O_ring Id_func) f OU_f)
(g_ : transf (sieve_mod (mod_loc_sieve D F f)) Id_func (F ∘>> O) Id_func )
// instead? (v : hom V (sieve_mod (mod_loc_sieve D f)) Id_func)
[V : func Terminal_cat S'] (v : hom V (Unit_mod Id_func U) Id_func) (f_inv : ring_inv (mod_ring_ring V F O_ring Id_func) (v '∘ (_)_'∘> f )) ⊢
ring_morph_fun (ring_loc_elim  Of_loc (mod_ring_con_ring_morph v F O_ring Id_func) f_inv) (mod_loc_elim D F f Of_loc g_ )
 ≡ (mod_loc_sieve_intro_hom D F f v f_inv) '∘ g_ ;

constant symbol mod_pullb_mod_loc : Π [S : cat] [O : mod S Terminal_cat] [O_ring : mod_ring O] (D : mod_loc O_ring),
Π [S'] (F : func S' S), mod_loc (mod_pullb_mod_ring O_ring F );

rule (mod_loc_sieve (mod_pullb_mod_loc $D $F0) $F $f)  
↪ (mod_loc_sieve $D ($F ∘> $F0) $f);
rule (mod_loc_sieve_intro_hom (mod_pullb_mod_loc $D $F0) $F $f $v $f_inv)  
↪ (mod_loc_sieve_intro_hom $D ($F ∘> $F0) $f $v $f_inv);
rule (mod_loc_elim (mod_pullb_mod_loc $D $F0) $F $f $Of_loc)  
↪ (mod_loc_elim $D ($F ∘> $F0) $f $Of_loc);


// --------------------------------------------
// # SCHEMES
// ## SLICE SITE, CONTINUOUS SITE MORPHISM WITH CONTINUOUS RIGHT ADJOINT


injective symbol slice_cat [S : cat] [I] (U : func I S) : cat
≔  Context_cat  (Comma_con_catd (Unit_mod Id_func U) (Terminal_catd _) );
injective symbol slice_proj_func [S : cat] [I] (U : func I S) : func (slice_cat U) S
≔  Context_elimCat_func (Comma_con_catd (Unit_mod Id_func U) (Terminal_catd _) );
constant symbol slice_site : Π [S : cat] (S_site : site S) [I] (U : func I S), 
site (slice_cat U);

//TODO: REVIEW CAREFULLY HERE

/// similar application of functor uses covariant variable, so ok the non-id F
constant symbol func_sieve_transf: Π [S : cat] [T : cat] (F : func S T),
transf (sieve S Terminal_cat ) F (sieve T Terminal_cat ) Id_func;
   
/// similar application of functor uses covariant variable, so ok the non-id F
constant symbol func_sieve_mod_transf: Π [S : cat] [T : cat] (F : func S T) [I] [U : func I S]
(ff : hom U (sieve S Terminal_cat ) (Terminal_func _)),
transf (sieve_mod ff) F (sieve_mod (func_sieve_transf F ∘' ff)) Id_func;

constant symbol site_morph: Π [S : cat] (S_site : site S) [T : cat] (T_site : site T) (F : func S T) (G : func T S), TYPE;

symbol site_morph_adj : Π [S : cat] [S_site : site S] [T : cat] [T_site : site T] [F : func S T] [G : func T S],
site_morph S_site T_site F G →  adj F G;

symbol site_morph_continous: Π [S : cat] [S_site : site S] [T : cat] [T_site : site T] [F : func S T] [G : func T S],
site_morph S_site T_site F G → 
transf (smod_mod (ssieve S_site Terminal_cat )) F (smod_mod (ssieve T_site Terminal_cat )) Id_func;

rule ssieve_sieve $T_site ((@site_morph_continous _ _ _ _ $F $G $FG_morph) ∘' $ff)
↪ func_sieve_transf $F ∘' (ssieve_sieve _ $ff);

// only one closed thing can cover has to be preserved, it the max sieve
rule (@site_morph_continous _ $S_site _ $T_site $F $G $FG_morph) ∘' (maximal_ssieve $S_site _ _)
↪ maximal_ssieve $T_site _ _;

symbol site_morph_preim_continous: Π [S : cat] [S_site : site S] [T : cat] [T_site : site T] [F : func S T] [G : func T S],
site_morph S_site T_site F G → 
transf (smod_mod (ssieve T_site Terminal_cat )) G (smod_mod (ssieve S_site Terminal_cat )) Id_func;

rule ssieve_sieve $S_site (@site_morph_preim_continous _ _ _ _ $F $G $FG_morph ∘' $ff)
↪ func_sieve_transf $G ∘' (ssieve_sieve _ $ff);

// EARLIER ATTEMPTS AT FORMULATION OF COCONTINOUS, BUT NOT NECESSARY BECAUSE RIGHT ADJOINT IS CONTINUOUS
// continuous radj -> cocontinu ladj... semantically.. but apparently not grammatically
// constant symbol site_morph_cocontinous: Π [S : cat] [S_site : site S] [T : cat] [T_site : site T] [F : func S T] [G : func T S],
// site_morph S_site T_site F G → 
// Π [U : func Terminal_cat S], hom (U ∘> F) (sieve T Terminal_cat) Id_func → hom U (sieve S Terminal_cat) Id_func;
// constant symbol site_morph_cocontinous: Π [S : cat] [S_site : site S] [T : cat] [T_site : site T] [F : func S T] [G : func T S],
// site_morph S_site T_site F G → 
// Π [U : func Terminal_cat S], hom U (F ∘>> (sieve T Terminal_cat)) Id_func → hom (U ∘> F) (G ∘>> (sieve S Terminal_cat)) Id_func;


// ref: stacks project 7.22 Cocontinuous functors which have a right adjoint
// https://stacks.math.columbia.edu/tag/00XW
// pushforward sheaf, when continuous-cocontinuous slice-projection-functor with continuous right adjoint
symbol site_morph_pushforward_smod : Π [S : cat] [S_site : site S] [T : cat] [T_site : site T] [F : func S T] [G : func T S],
site_morph S_site T_site F G → Π [B : cat],
smod S_site B → smod T_site B;

rule smod_mod (@site_morph_pushforward_smod _ _ _ _ $F $G _ _ $R) ↪ 
 ($G ∘>> smod_mod $R);

// pullback sheaf, when continuous-cocontinuous slice-projection-functor with continuous right adjoint
symbol site_morph_pullback_smod : Π [S : cat] [S_site : site S] [T : cat] [T_site : site T] [F : func S T] [G : func T S],
site_morph S_site T_site F G → Π [B : cat],
smod T_site B → smod S_site B; 
rule smod_mod (@site_morph_pullback_smod _ _ _ _ $F $G _ _ $R) ↪ 
 ($F ∘>> smod_mod $R);

// stacks project "technical" Lemma 7.20.4. https://stacks.math.columbia.edu/tag/00XM
rule @site_morph_pullback_smod _ _ _ _ $F $G _ _ (mod_smod _ $R)
↪ mod_smod _ ($F ∘>> $R);

//TODO: complete the adjunction specification
constant symbol adj_mod_adjL : Π [S : cat] [T : cat] [F : func S T] [G : func T S]
(FG_ad : adj F G) [I] [L : mod T I] [B : cat] [H : func I B] (R : mod S B),
transf L Id_func (G ∘>> R) H
→ transf (F ∘>> L) Id_func R H;

symbol site_morph_mod_adjL : Π [S : cat] [S_site : site S] [T : cat] [T_site : site T] [F : func S T] [G : func T S] (Sm : site_morph S_site T_site F G) [I][L : smod T_site I][B : cat] [H : func I B] (R : smod S_site B),
transf (smod_mod L) Id_func (smod_mod (site_morph_pushforward_smod Sm R)) H
→ transf (smod_mod (site_morph_pullback_smod Sm L)) Id_func (smod_mod R) H;

// interaction betwen adjunction-transposition operations in the slice and base,  is via gluing.
rule site_morph_mod_adjL $Sm $R (glue _ _ _ $r_)
↪ (glue _ _ _ (adj_mod_adjL (site_morph_adj $Sm) (smod_mod $R) $r_));

// transf L Id_func (G ∘>> smod_mod R) H
assert  [S : cat] [S_site : site S] [T : cat] [T_site : site T] [F : func S T] [G : func T S]
(Sm : site_morph S_site T_site F G) [B : cat]  (R : smod S_site B) [I] [H : func I B] 
(L : mod T I)
(r_ : transf L Id_func (smod_mod (site_morph_pushforward_smod Sm R)) H) ⊢
site_morph_mod_adjL Sm R (glue _ _ _ r_)
≡ (glue _ _ _ (adj_mod_adjL (site_morph_adj Sm) (smod_mod R) r_));
//DONT ERASE: the alternative wont work:
//    adj_mod_adjL (site_morph_adj Sm) (smod_mod R) (glue _ _ _ r_);
//transf (F ∘>> smod_mod (mod_smod T_site L)) Id_func (smod_mod R) H
//transf (smod_mod (mod_smod S_site (F ∘>> L))) Id_func (smod_mod R) H
// typing for adj in mod and smod is OK but normally they should not interact because smod_mod should be really contanst not only injective for convenience. 
// in fact the rewrite rule is an example of the interaction betwen adjunction-transposition operations in the slice and base 
type λ [S : cat] [S_site : site S] [T : cat] [T_site : site T] [F : func S T] [G : func T S]
(Sm : site_morph S_site T_site F G) [B : cat]  (R : smod S_site B) [I] [H : func I B] 
(L : smod T_site I)
(r_ : transf (smod_mod L) Id_func (smod_mod (site_morph_pushforward_smod Sm R)) H),
 site_morph_mod_adjL Sm R r_
= (adj_mod_adjL (site_morph_adj Sm) (smod_mod R) r_) ;


//TODO: COMPLETE THE ADJUNCTION DETAILS
//REVIEW use eta formulation instead of right transpose formulation?
constant symbol adj_mod_adjR : Π [S : cat] [T : cat] [F : func S T] [G : func T S]
(FG_ad : adj F G) [I] (L : mod T I) [B : cat] [H : func I B] [R : mod S B],
transf (F ∘>> L) Id_func R H
→ transf L Id_func (G ∘>> R) H;
symbol site_morph_mod_adjR : Π [S : cat] [S_site : site S] [T : cat] [T_site : site T] [F : func S T] [G : func T S] (Sm : site_morph S_site T_site F G) [I] (L : smod T_site I) [B : cat] [H : func I B] [R : smod S_site B],
transf (smod_mod (site_morph_pullback_smod Sm L)) Id_func (smod_mod R) H
→ transf (smod_mod L) Id_func (smod_mod (site_morph_pushforward_smod Sm R)) H;
///REVIEW: would cause problems with defined pullback $F ∘>> $L  .. wrap it in its own symbol?
//REVIEW: is this logically provable so that not necessary as rule? YES logically provable because it is transpose of other rule
rule @site_morph_mod_adjR _ _ _ _ $F $G $Sm _ (mod_smod $T_site $L) _ _ _ (glue _ $R ($F ∘>> $L) $r_)
↪ (glue _ (site_morph_pushforward_smod $Sm $R) _ (adj_mod_adjR (site_morph_adj $Sm) $L $r_));
assert [S : cat] [S_site : site S] [T : cat] [T_site : site T] [F : func S T] [G : func T S]
(Sm : site_morph S_site T_site F G) [B : cat]  (R : smod S_site B) [I] [H : func I B] 
(L : mod T I)
(r_ : transf (F ∘>> L) Id_func (smod_mod R) H) ⊢
site_morph_mod_adjR Sm (mod_smod T_site L) (glue _ R (F ∘>> L) r_)
≡ (glue _ (site_morph_pushforward_smod Sm R) _ (adj_mod_adjR (site_morph_adj Sm) L r_));


// --------------------------------------------
// # SCHEMES
// ## AFFINE SCHEME INTERFACE: PART 1, SLICE OF AFFINE SCHEME IS AFFINE


// struct for locally ringed site, used as param for affine scheme and scheme
//TODO? move site param out? because sharing with struct_cov_sieve in the spec of `scheme` ...
constant symbol struct_mod_loc : TYPE;
constant symbol Struct_mod_loc : Π [Ml_cat : cat] [Ml_site: site Ml_cat] [Ml_smod : smod Ml_site Terminal_cat] [Ml_mod_ring : mod_ring (smod_mod Ml_smod)] (Ml_mod_loc : mod_loc Ml_mod_ring), struct_mod_loc;

symbol mod_loc_cat : Π (Ml : struct_mod_loc), cat;
symbol mod_loc_site : Π (Ml : struct_mod_loc), site (mod_loc_cat Ml);
symbol mod_loc_smod : Π (Ml : struct_mod_loc), smod (mod_loc_site Ml) Terminal_cat;
symbol mod_loc_mod_ring : Π (Ml : struct_mod_loc), mod_ring (smod_mod (mod_loc_smod Ml));
symbol mod_loc_mod_loc : Π (Ml : struct_mod_loc), mod_loc (mod_loc_mod_ring Ml);

rule mod_loc_cat (@Struct_mod_loc $Ml_cat $Ml_site $Ml_smod $Ml_mod_ring $Ml_mod_loc) ↪ $Ml_cat;
rule mod_loc_site (@Struct_mod_loc $Ml_cat $Ml_site $Ml_smod $Ml_mod_ring $Ml_mod_loc) ↪ $Ml_site;
rule mod_loc_smod (@Struct_mod_loc $Ml_cat $Ml_site $Ml_smod $Ml_mod_ring $Ml_mod_loc) ↪ $Ml_smod;
rule mod_loc_mod_ring (@Struct_mod_loc $Ml_cat $Ml_site $Ml_smod $Ml_mod_ring $Ml_mod_loc) ↪ $Ml_mod_ring;
rule mod_loc_mod_loc (@Struct_mod_loc $Ml_cat $Ml_site $Ml_smod $Ml_mod_ring $Ml_mod_loc) ↪ $Ml_mod_loc;

injective symbol mod_loc_ring (Ml : struct_mod_loc) [I] (U : func I (mod_loc_cat Ml)) : ring (hom_type U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)) 
≔ mod_ring_ring U Id_func (mod_loc_mod_ring Ml) (Terminal_func _);

// affine schmes
constant symbol ascheme : Π (Ml : struct_mod_loc), TYPE;

// primitive Zarisky  D(r)... for affine ringed_locally is singleton sieve on this 
constant symbol ascheme_inv_func : Π [Ml : struct_mod_loc] (Af : ascheme Ml),
/* when U is Id_func (therefore diagram of rings is determined at Terminal_obj), this is the usual ring */
Π [I] [U : func I (mod_loc_cat Ml)] (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)), func I (mod_loc_cat Ml);

//TODO: TO COMPLETE: all constructors must be relativized, have versions (witnesses) in the slice
constant symbol ascheme_inv_slice_func : Π [Ml : struct_mod_loc] (Af : ascheme Ml),
Π [I] [U : func I (mod_loc_cat Ml)] (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)), func I (slice_cat U);
rule ascheme_inv_slice_func $Af $r ∘> Context_elimCat_func _ 
↪ ascheme_inv_func $Af $r;

///extensional (non intrinsically-manifest) truncation. question: truncate only in the base subcat?
// used to extensionally manually prove the compatibility of cocones over diagrams of joins
constant symbol ascheme_poset_truncate : Π [Ml : struct_mod_loc] (Af : ascheme Ml),
Π [I] [U : func I _] [r s : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)]
(f f' : hom (ascheme_inv_func Af r) (Unit_mod Id_func (ascheme_inv_func Af s)) Id_func),
 τ  (f = f');

//todo: review the best version of possible formulations; combine the radicals and multiplication?

// both multiplication on the left and the right seem to be required
constant symbol ascheme_multL_hom : Π [Ml : struct_mod_loc] (Af : ascheme Ml),
Π [I] [U : func I _] (s r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)), 
hom (ascheme_inv_func Af (ring_mult (mod_loc_ring Ml U) s r)) (Unit_mod Id_func (ascheme_inv_func Af r)) Id_func;
constant symbol ascheme_multR_hom : Π [Ml : struct_mod_loc] (Af : ascheme Ml),
Π [I] [U : func I _] (s r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)), 
hom (ascheme_inv_func Af (ring_mult (mod_loc_ring Ml U) s r)) (Unit_mod Id_func (ascheme_inv_func Af s)) Id_func;

// radical
constant symbol ascheme_radical_hom : Π [Ml : struct_mod_loc] (Af : ascheme Ml),
Π [I] [U : func I _] (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)) (n : nat), 
hom (ascheme_inv_func Af r) (Unit_mod Id_func (ascheme_inv_func Af (ring_exp (mod_loc_ring Ml U) r n))) Id_func;

// this congruent/relativized version don't seem necessary anymore because everything is intrinsically relative under a slice
// constant symbol ascheme_radical_hom : Π [Ml : struct_mod_loc] (Af : ascheme Ml),
// Π [I] [U : func I _] (s r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)), 
// hom (ascheme_inv_func Af (ring_mult (mod_loc_ring Ml U) s r)) (Unit_mod Id_func (ascheme_inv_func Af (ring_mult (mod_loc_ring Ml U) s (ring_mult (mod_loc_ring Ml U) r r)))) Id_func;

// profunctor/module sections are localizations of rings, in two ways

constant symbol ascheme_mod_ring_loc : Π [Ml : struct_mod_loc] (Af : ascheme Ml),
Π [I] [U : func I _] (f : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
ring_loc (mod_loc_ring Ml U) f (mod_loc_ring Ml (ascheme_inv_func Af f));

rule (@ascheme_multL_hom $Ml $Af _ $U $s $r) '∘ (_) _'∘> (ring_loc_intro (ascheme_mod_ring_loc $Af $r) $f $n)
  ↪ ring_loc_intro (ascheme_mod_ring_loc $Af (ring_mult (mod_loc_ring $Ml $U) $s $r)) (ring_mult (mod_loc_ring $Ml $U) (ring_exp (mod_loc_ring $Ml $U) $s $n) $f) $n;

assert [Ml : struct_mod_loc] (Af : ascheme Ml) [I] [U : func I _] (r s : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)) f n ⊢
(ascheme_multL_hom Af s r) '∘ (_) _'∘> (ring_loc_intro (ascheme_mod_ring_loc Af r) f n)
≡ ring_loc_intro (ascheme_mod_ring_loc Af (ring_mult (mod_loc_ring Ml U) s r)) (ring_mult (mod_loc_ring Ml U) (ring_exp (mod_loc_ring Ml U) s n) f) n;

constant symbol ascheme_slice_mod_ring_loc : Π [Ml : struct_mod_loc] (Af : ascheme Ml), 
Π /* in usual ring */(r : hom Id_func (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
 ring_loc (mod_loc_ring Ml Id_func) r
      (mod_ring_ring Id_func (slice_proj_func (ascheme_inv_func Af r)) (mod_loc_mod_ring Ml) (Terminal_func _));

// invertibility support sieve is generated by a singleton arrow at a basic object

constant symbol ascheme_mod_loc_sieve_intro_hom : Π [Ml : struct_mod_loc] (Af : ascheme Ml),
Π [I] [U : func I _] (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
hom (ascheme_inv_func Af r) (sieve_mod (mod_loc_sieve (mod_loc_mod_loc Ml) Id_func/* gen F will be used in pullb */ r)) Id_func;

constant symbol ascheme_mod_loc_sieve_elim_transf : Π [Ml : struct_mod_loc] (Af : ascheme Ml),
Π [I] [U : func I _] (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
Π [D] [G : func I D] [T : mod _ D],
hom (ascheme_inv_func Af r) T G →
transf (sieve_mod (mod_loc_sieve (mod_loc_mod_loc Ml) Id_func r)) Id_func T G;

rule (ascheme_mod_loc_sieve_intro_hom $Af $r) '∘ ascheme_mod_loc_sieve_elim_transf $Af $r $t
↪ $t;

//convenience, not necessary
symbol ascheme_mod_loc_sieve_intro_cat_hom [Ml : struct_mod_loc] (Af : ascheme Ml)
 [I] [U : func I _] (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)):
hom (ascheme_inv_func Af r) (Unit_mod Id_func U) Id_func
≔ (ascheme_mod_loc_sieve_intro_hom Af r) '∘ Context_elimMod_transf (sieve_modd (mod_loc_sieve (mod_loc_mod_loc Ml) Id_func r)) ;

// this is the product/pullback operation in the site

constant symbol ascheme_slice_preim_func : Π [Ml : struct_mod_loc] (Af : ascheme Ml),
Π [I] [U : func I _] (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
func (mod_loc_cat Ml) (slice_cat (ascheme_inv_func Af r));

constant symbol ascheme_site_morph : Π [Ml : struct_mod_loc] (Af : ascheme Ml),
Π [I] [U : func I _] (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
site_morph (slice_site (mod_loc_site Ml) (ascheme_inv_func Af r)) (mod_loc_site Ml) (slice_proj_func (ascheme_inv_func Af r)) (ascheme_slice_preim_func Af r) ;

// the slice of affine schme is affine scheme

constant symbol ascheme_slice_ascheme : Π [Ml : struct_mod_loc] (Af : ascheme Ml),
Π [I] [U : func I _] (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
 let W ≔  (ascheme_inv_func Af r) in

ascheme (@Struct_mod_loc (slice_cat W) (slice_site (mod_loc_site Ml) W) 
 (site_morph_pullback_smod (ascheme_site_morph Af r) (mod_loc_smod Ml))
 (mod_pullb_mod_ring (mod_loc_mod_ring Ml) (slice_proj_func W))
 (mod_pullb_mod_loc (mod_loc_mod_loc Ml) (slice_proj_func W)));


// --------------------------------------------
// # SCHEMES
// ## SCHEME INTERFACE, AFFINE COVER

constant symbol struct_cov_sieve : Π [Ml_cat : cat] (Ml_site : site Ml_cat), TYPE;
constant symbol Struct_cov_sieve : Π [Ml_cat : cat] (Ml_site : site Ml_cat) [Cs_cat : cat] [Cs_func : func Cs_cat Ml_cat] (Cs_hom : hom Cs_func (sieve Ml_cat Terminal_cat) (Terminal_func _)), struct_cov_sieve Ml_site;

symbol cov_sieve_cat : Π [Ml_cat : cat] [Ml_site : site Ml_cat] (Cs : struct_cov_sieve Ml_site), cat;
symbol cov_sieve_func : Π [Ml_cat : cat] [Ml_site : site Ml_cat] (Cs : struct_cov_sieve Ml_site), func (cov_sieve_cat Cs) Ml_cat;
symbol cov_sieve_hom : Π [Ml_cat : cat] [Ml_site : site Ml_cat] (Cs : struct_cov_sieve Ml_site), hom (cov_sieve_func Cs) (sieve Ml_cat Terminal_cat) (Terminal_func _);

rule cov_sieve_cat (@Struct_cov_sieve $Ml_cat $Ml_site $Cs_cat $Cs_func $Cs_hom) ↪ $Cs_cat;
rule cov_sieve_func (@Struct_cov_sieve $Ml_cat $Ml_site $Cs_cat $Cs_func $Cs_hom) ↪ $Cs_func;
rule cov_sieve_hom (@Struct_cov_sieve $Ml_cat $Ml_site $Cs_cat $Cs_func $Cs_hom) ↪ $Cs_hom;

//REVIEW ALTERNATIVE?: here cov_sieve_hom is not (always) constant.. so when it is defined/computed the knowledge that it is covering comes from elesewhere
rule (@cov_sieve_hom $Ml_cat $Ml_site $Cs) '∘ (sieve_ssieve $Ml_site _)
 ↪ maximal_ssieve $Ml_site _ _ ;

// schemes

//TODO pop parameter `site` out for sharing?
// so scheme spec on top of params adds that pullbacking is slice site morphism and that slice is aschme

constant symbol scheme : Π (Ml : struct_mod_loc) (Cs : struct_cov_sieve (mod_loc_site Ml)), TYPE;

// this is the product/pullback operation in the site

constant symbol scheme_slice_preim_func : Π [Ml : struct_mod_loc] [Cs : struct_cov_sieve (mod_loc_site Ml)] (Sc : scheme Ml Cs),
Π [I] (U : func I (mod_loc_cat Ml)), func (mod_loc_cat Ml) (slice_cat U);

constant symbol scheme_site_morph : Π [Ml : struct_mod_loc] [Cs : struct_cov_sieve (mod_loc_site Ml)] (Sc : scheme Ml Cs),
Π [I] (U : func I (mod_loc_cat Ml)), site_morph (slice_site (mod_loc_site Ml) U) (mod_loc_site Ml) (slice_proj_func U) (scheme_slice_preim_func Sc U) ;

// the slice of schme over the affine cover is affine scheme

constant symbol scheme_slice_ascheme : Π [Ml : struct_mod_loc] [Cs : struct_cov_sieve (mod_loc_site Ml)] (Sc : scheme Ml Cs),
Π [U : func (cov_sieve_cat Cs)/*TODO: gen*/ (mod_loc_cat Ml)] (u : hom U (sieve_mod (cov_sieve_hom Cs)) Id_func/*TODO: gen JI*/ ),

ascheme (@Struct_mod_loc (slice_cat U) (slice_site (mod_loc_site Ml) U)
  (site_morph_pullback_smod (scheme_site_morph Sc U) (mod_loc_smod Ml))
  (mod_pullb_mod_ring (mod_loc_mod_ring Ml) (slice_proj_func U))
  (mod_pullb_mod_loc (mod_loc_mod_loc Ml) (slice_proj_func U)));


// --------------------------------------------
// # SCHEMES
// ## AFFINE SCHEME INTERFACE: PART 2, INTERFACE FOR JOIN COVER BY BASIC OPENS


// skewed arguments: general left argument but basic right argument in the join/meet (necessarily both) operations, for easier confluence/metatheoretical analysis, but computationally the alternative should be feasible
// maybe join is misleading word, it is not the limit/universal property directly which is of interest, but the covering sieve property whis is of interest

constant symbol ascheme_join_func : Π [Ml : struct_mod_loc] (Af : ascheme Ml) [I] [U : func I (mod_loc_cat Ml)] (W : func I (slice_cat U)) (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
func I (slice_cat U);

constant symbol ascheme_join_introL_slice_hom :
Π [Ml : struct_mod_loc] (Af : ascheme Ml) [I] [U : func I (mod_loc_cat Ml)] (W : func I (slice_cat U)) (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
hom W (Unit_mod Id_func (ascheme_join_func Af W r)) Id_func;

constant symbol ascheme_join_introL_hom :
Π [Ml : struct_mod_loc] (Af : ascheme Ml) [I] [U : func I (mod_loc_cat Ml)] (W : func I (slice_cat U)) (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
hom (W ∘> (slice_proj_func U)) (Unit_mod Id_func ((ascheme_join_func Af W r) ∘> (slice_proj_func U))) Id_func;

rule (((Func_cov_hom (slice_proj_func $U) Id_func) ∘>'_ (_)) ∘' (@ascheme_join_introL_slice_hom _ $Af _ $U $W $r))
↪ (ascheme_join_introL_hom $Af $W $r);

constant symbol ascheme_join_introR_hom :
Π [Ml : struct_mod_loc] (Af : ascheme Ml) [I] [U : func I (mod_loc_cat Ml)] (W : func I (slice_cat U)) (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
hom (ascheme_inv_func Af r) (Unit_mod Id_func ((ascheme_join_func Af W r) ∘> (slice_proj_func U))) Id_func;

constant symbol ascheme_join_sieve : Π [Ml : struct_mod_loc] (Af : ascheme Ml) [I] [U : func I (mod_loc_cat Ml)] (W : func I (slice_cat U)) (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
hom ((ascheme_join_func Af W r) ∘> (slice_proj_func U)) (sieve (mod_loc_cat Ml) Terminal_cat) (Terminal_func _);

rule (@ascheme_join_sieve $Ml $Af $I $U $W $r) '∘ (sieve_ssieve (mod_loc_site $Ml) Terminal_cat)
↪ maximal_ssieve (mod_loc_site $Ml) ((ascheme_join_func $Af $W $r) ∘> (slice_proj_func $U)) (Terminal_func _);

constant symbol ascheme_join_sieve_introL_hom : Π [Ml : struct_mod_loc] (Af : ascheme Ml) [I] [U : func I (mod_loc_cat Ml)] (W : func I (slice_cat U)) (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
hom (W ∘> (slice_proj_func U)) (sieve_mod (ascheme_join_sieve Af W r)) Id_func ;

constant symbol ascheme_join_sieve_introR_hom : Π [Ml : struct_mod_loc] (Af : ascheme Ml) [I] [U : func I (mod_loc_cat Ml)] (W : func I (slice_cat U)) (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
hom (ascheme_inv_func Af r) (sieve_mod (ascheme_join_sieve Af W r)) Id_func ;

symbol ascheme_bottomJoin_el : Π [Ml : struct_mod_loc] (Af : ascheme Ml) [I] [U : func I (mod_loc_cat Ml)] (W : func I (slice_cat U)) (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
   hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _);

// skew arguments sizes for easier confluence?
rule @ascheme_bottomJoin_el $Ml $Af _ $U (@ascheme_join_func $Ml $Af _ $U $W $s) $r
↪ (ring_mult (mod_loc_ring $Ml $U) (@ascheme_bottomJoin_el _ $Af _ $U $W $s) $r);

symbol ascheme_join_introM_hom :
Π [Ml : struct_mod_loc] (Af : ascheme Ml) [I] [U : func I (mod_loc_cat Ml)] (W : func I (slice_cat U)) (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
hom (ascheme_inv_func Af (ascheme_bottomJoin_el Af W r)) (Unit_mod Id_func ((ascheme_join_func Af W r) ∘> (slice_proj_func U))) Id_func;

constant symbol ascheme_join_sieve_introM_hom : Π [Ml : struct_mod_loc] (Af : ascheme Ml) [I] [U : func I (mod_loc_cat Ml)] (W : func I (slice_cat U)) (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
hom (ascheme_inv_func Af (ascheme_bottomJoin_el Af W r))  (sieve_mod (ascheme_join_sieve Af W r)) Id_func ;

symbol ascheme_bottomJoin_elimL_hom :
Π [Ml : struct_mod_loc] (Af : ascheme Ml) [I] [U : func I (mod_loc_cat Ml)] (W : func I (slice_cat U)) (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
hom (ascheme_inv_func Af (ascheme_bottomJoin_el Af W r)) (Unit_mod Id_func (W ∘> (slice_proj_func U))) Id_func;

symbol ascheme_bottomJoin_elimR_hom :
Π [Ml : struct_mod_loc] (Af : ascheme Ml) [I] [U : func I (mod_loc_cat Ml)] (W : func I (slice_cat U)) (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)),
hom (ascheme_inv_func Af (ascheme_bottomJoin_el Af W r)) (Unit_mod Id_func (ascheme_inv_func Af r)) Id_func;

rule (@ascheme_bottomJoin_elimL_hom $Ml $Af _ $U $W $r)
  '∘ (_)_'∘> ((ascheme_join_introL_hom $Af $W $r))
↪ (@ascheme_join_introM_hom $Ml $Af _ $U $W $r);

rule (@ascheme_bottomJoin_elimR_hom $Ml $Af _ $U $W $r)
  '∘ (_)_'∘> (ascheme_join_introR_hom $Af $W $r)  
↪ (@ascheme_join_introM_hom $Ml $Af _ $U $W $r);

rule @ascheme_bottomJoin_elimL_hom _ $Af _ $U (@ascheme_join_func _ $Af _ $U $W $s) $r
↪  ((ascheme_multR_hom $Af (@ascheme_bottomJoin_el _ $Af _ _ $W $s) $r) 
'∘ (_)_'∘> (@ascheme_join_introM_hom _ $Af _ _ $W $s)) ;

//ascheme_join_introM_hom would be used here, if right argument was general
rule @ascheme_bottomJoin_elimR_hom _ $Af _ $U (@ascheme_join_func _ $Af _ $U $W $s) $r
↪  (ascheme_multL_hom $Af (@ascheme_bottomJoin_el _ $Af _ _ $W $s) $r)  ;

constant symbol ascheme_join_sieve_induction : Π [Ml : struct_mod_loc] (Af : ascheme Ml) [I] [U : func I (mod_loc_cat Ml)] [W : func I (slice_cat U)] [r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)] 
[B] [T : smod (mod_loc_site Ml) B] [G : func I B]  
(t_l : hom (W ∘> slice_proj_func U) (smod_mod T) G ) 
(t_m : hom (ascheme_inv_func Af (ascheme_bottomJoin_el Af W r))  (smod_mod T) G )
(t_r: hom (ascheme_inv_func Af r) (smod_mod T) G),
  homd (ascheme_bottomJoin_elimL_hom Af W r) (Comma_con_intro_funcd (Terminal_catd _) t_m)
  (Unit_modd Id_funcd (Comma_con_intro_funcd (Terminal_catd _) t_l)) Id_funcd →
  homd (ascheme_bottomJoin_elimR_hom Af W r) (Comma_con_intro_funcd (Terminal_catd _) t_m)
  (Unit_modd Id_funcd (Comma_con_intro_funcd (Terminal_catd _) t_r)) Id_funcd →
transf (sieve_mod (ascheme_join_sieve Af W r)) Id_func (smod_mod T) G;

// NOTE: USED SLICE CATEGORY TO REQUIRE THAT THIS EQUATION CONDITION BE DEFINITIONAL/COMPUTATIONAL 
// BUT THEREAFTER EVEM WITH A (METAFRAMEWORK's) PROPOSITIONAL EQUALITY IT IS STILL POSSIBLE TO BUILD A SLICE CONE (WITH TRANSPORTED GROUNDING) BUT WITHOUT GUARANTY OF COMPUTATION 
// τ ( ((ascheme_bottomJoin_elimL_hom U r) '∘ (_)_'∘> t_l) = t_m )  →
// τ ( ((ascheme_bottomJoin_elimR_hom U r) '∘ (_)_'∘> t_r) = t_m )  →
/// NOTE: simpler version is possible because site is poset...

rule  (ascheme_join_sieve_introM_hom $Af $W $r) '∘ (@ascheme_join_sieve_induction _ $Af  _ $U $W $r _ _ _ $t_l $t_m $t_r _ _) ↪ $t_m;
rule  (ascheme_join_sieve_introL_hom $Af $W $r) '∘ (@ascheme_join_sieve_induction _ $Af  _ $U $W $r _ _ _ $t_l $t_m $t_r _ _) ↪ $t_l;
rule  (ascheme_join_sieve_introR_hom $Af $W $r) '∘ (@ascheme_join_sieve_induction _ $Af  _ $U $W $r _ _ _ $t_l $t_m $t_r _ _) ↪ $t_r;


// --------------------------------------------
// # SCHEMES
// ## AFFINE SCHEME INTERFACE: PART 3, INTERFACE FOR UNIMODULAR COVER OF A BASIC OPEN


// simplified version for demo, TODO: some algebra here
constant symbol ascheme_unimodular_sieve : Π [Ml : struct_mod_loc] (Af : ascheme Ml) [I] [U : func I (mod_loc_cat Ml)] /* here parameter j for r_j */ (r1 r2 : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)), 
//TODO: some algebra here (s_inv : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _) ≔ √^n ( a1 r1 + a2 r2)) ... but simplified for now 
hom (ascheme_inv_func Af (ring_add (mod_loc_ring Ml U) r1 r2)) (sieve (mod_loc_cat Ml) Terminal_cat) (Terminal_func _);

rule (@ascheme_unimodular_sieve $Ml $Af _ $U $r1 $r2) '∘ (sieve_ssieve (mod_loc_site $Ml) Terminal_cat)
↪ maximal_ssieve (mod_loc_site $Ml) (ascheme_inv_func $Af (ring_add (mod_loc_ring $Ml $U) $r1 $r2)) (Terminal_func _);

constant symbol ascheme_unimodular_sieve_intro1_hom : Π [Ml : struct_mod_loc] (Af : ascheme Ml) [I] [U : func I (mod_loc_cat Ml)] (r1 r2 : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)) /* here parameter j for r_j */,
hom (ascheme_inv_func Af (ring_mult (mod_loc_ring Ml U) r1 (ring_add (mod_loc_ring Ml U) r1 r2))) (sieve_mod (ascheme_unimodular_sieve Af r1 r2)) Id_func ;

constant symbol ascheme_unimodular_sieve_intro2_hom : Π [Ml : struct_mod_loc] (Af : ascheme Ml) [I] [U : func I (mod_loc_cat Ml)] (r1 r2 : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)) /* here parameter j for r_j */,
hom (ascheme_inv_func Af (ring_mult (mod_loc_ring Ml U) r2 (ring_add (mod_loc_ring Ml U) r1 r2))) (sieve_mod (ascheme_unimodular_sieve Af r1 r2)) Id_func ;

rule (@ascheme_unimodular_sieve_intro1_hom $Ml $Af _ $U $r1 $r2) '∘ Context_elimMod_transf (sieve_modd(ascheme_unimodular_sieve $Af $r1 $r2))
↪ (ascheme_multL_hom $Af $r1 (ring_add (mod_loc_ring $Ml $U) $r1 $r2) )  ;

rule (@ascheme_unimodular_sieve_intro2_hom $Ml $Af _ $U $r1 $r2) '∘ Context_elimMod_transf (sieve_modd(ascheme_unimodular_sieve $Af $r1 $r2))
↪ (ascheme_multL_hom $Af $r2 (ring_add (mod_loc_ring $Ml $U) $r1 $r2) ) ;

//TODO: finish this map which implements the computation in the unimodular localization isomorphisms

//WARNING SUBTLE
type λ [Ml : struct_mod_loc] (Af : ascheme Ml) [I] [U : func I (mod_loc_cat Ml)] /* here parameter j for r_j */ (r1 r2 : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _))  [B : cat] [T : smod (mod_loc_site Ml) B] [G : func I B] 
(t_ : transf (sieve_mod (ascheme_unimodular_sieve Af r1 r2)) Id_func (smod_mod T) G),

(eta_smod_transf (mod_loc_site Ml) _ ((Func_cov_hom _ Id_func) '∘ (maximal_sieve_intro_transf 
(ascheme_inv_func Af ((ring_add (mod_loc_ring Ml U) r1 r2))) (Terminal_func _)) ))
 '∘ (glue (mod_loc_site Ml) _  (sieve_mod (ascheme_unimodular_sieve Af r1 r2)) t_ );
///here was the typing issue... because smod_mod is injective, then the smod need to agree. therefore added adhoc rule that ssieve_smod of maximal_ssieve is smod of Unit_mod ... TODO: REDO THIS WITH A NEW smodd (dependent sheaves)
 // 1. (smod_mod (mod_smod (mod_loc_site Ml) (sieve_mod (maximal_sieve (ascheme_inv_func Af (ring_add (mod_loc_ring Ml U) r1 r2)) (Terminal_func I)))))
// 2. (smod_mod (mod_smod (mod_loc_site Ml) (sieve_mod (ascheme_unimodular_sieve Af r1 r2)))) 


print coerce_rule; // /!\ BUG, DONT USE, ONLY CONSOLE print unif_rule;


// --------------------------------------------
// # COMMENTS
//


/*
Kosta Dosen's functorial programming: A computational logic (coinductive) interface for schemes in algebraic geometry.

    [updated] https://github.com/1337777/cartier/blob/master/cartierSolution16.lp 

This is the continuation of an ongoing research programme of discovering a truly computational logic (Lambdapi type theory) for categories, profunctors, fibred categories, univalence, polynomial functors, sites, sheaves and schemes, in the style of Kosta Dosen [1].

Firstly, a glue operation for any sheaf `S` over the sheafification modality `mod_smod` is declared:

    constant symbol glue : Π [A B : cat] (A_site : site A)  [S : smod A_site B] [I : cat] [G : func I B] (L : mod A I),
transf L Id_func (smod_mod S) G
→  transf (smod_mod (mod_smod A_site L)) Id_func (smod_mod S) G; 

From which a glue operation for any sheaf `S` over the sieve-closure modality `sieve_ssieve` is defined, where `sieve` is the presheaf (profunctor …) which classifies sieves:

    symbol glue_sieve_mod_def : Π [A B : cat] (A_site : site A) [I : cat] [F : func I A]  [S : smod A_site B]  [G : func I B] [D : cat] [K : func I D] (ff : hom F (sieve A D) K),
transf (sieve_mod ff) Id_func (smod_mod S) G)
→  transf (smod_mod (ssieve_smod ((ff '∘ (sieve_ssieve A_site _))))) Id_func (smod_mod S) G ≔ glue …; 

Now a transformation (predicate) into the sieves-classifier (truth-values) `sieve` corresponds to a subprofunctor (fibred/dependent profunctor), such as the maximal sieve or the intersection sieve, but also a novel “sub sieve” construction.

And when the sieve-closure `sieve_ssieve` happens to evaluate to the maximal sieve, then this glue operation is indeed the expected inverse operation of the Yoneda action by sieve-elements. In short: Nicolas Tabareau [2] is only a formalization of the semantics of sheafification, not an actual computational logic; and moreover, its Definition 5.2 causes flaws: instead of “a subobject of E is dense in E if …”, it should be “a subobject P of E is dense in another subobject Q of E if …”.

Next, there are also (substructural) versions of this story in the presence of context: tensor-product context A⊗B ⊢ C, subtype (sum type) context Σ(a:A),P(a) ⊢ C, and dependent-type context (x:A)|B(x) ⊢ C(x). It is not necessary to use multi-categories and hyperdoctrines (categories with families …) to manage contexts, don’t be indoctrinated by Mikey [3] lol … Why? Because a question which is rarely entertained by logicians is:

    “Who are my end-users?” 

For dependent-type contexts, the answer lies in a (computational) implementation of the (usually semantic) context-extension operation:

    injective symbol Context_cat : Π [X : cat], catd X → cat;
injective symbol Context_elimCat_func : Π [X : cat] (A : catd X), func (Context_cat A) X;
injective symbol Context_intro_single_func : Π [Y : cat] [B : catd Y] [X : cat] (xy : func X Y), funcd (Terminal_catd X) xy B → func X (Context_cat B);
injective symbol Context_intro_func : Π [X Y : cat] [A : catd X] [B : catd Y] [xy : func X Y], funcd A xy B → func (Context_cat A) (Context_cat B);

For subtype contexts, the answer already lies in an implementation of sieves/subobject classifiers/universes as explained in the preceding paragraphs, and in the implementation of the Sigma-sum (along fibrations) and the Pi-product (along opfibrations …) of fibred categories/profunctors (with beck-chevalley-commutation along fibres):

    injective symbol Sigma_catd : Π [X : cat] (F : catd X) (Z : catd (Context_cat F)), catd X;
injective symbol Sigma_elim_funcd : Π [X : cat] (F : catd X) [Z : catd (Context_cat F)] [X'] (G : func X X') [C : catd X'], funcd Z ((Context_elimCat_func F) ∘> G) C → funcd (Sigma_catd F Z) G C;
injective symbol Pi_elim_funcd : Π [X : cat] [F : catd X] [Z : catd (Context_cat F)] [X'] [x : func X' X] [E : catd X'], funcd E x (Pi_catd F Z) → funcd (Fibre_catd E (Context_elimCat_func (Fibre_catd F x))) (Context_intro_func (Fibre_elim_funcd F x)) Z;

For tensor-product contexts, the answer lies in reformulating the elimination rule for the tensor product in multi-categories which says: if a:A, b:B ⊢ C then A⊗B ⊢ C. Each time that this rule would be used, instead its intention can be simulated by the Lambdapi end-user by manually (via macros …) adding a rewrite rule which outputs the intended body content of A⊗B ⊢ C when applied to a constructor ⟨a, b⟩. In short: multi-categories are to help the dummy end-user.

Next, the presentation of affine schemes is such that it exposes a logical interface/specification which computes; for example the structure sheaf `ascheme_mod_ring_loc` localized away from r : R has restrictions along D(s⋅r) ⊆ D(r) (and, substructurally, along explicit radicals D(r) ⊆ D(r^n) …) which compute (by the usual recasting of any sheaf element `f/r^n` as `(s^n)⋅f/(s⋅r)^n`):

    rule (@ascheme_mult_hom $Ml $Af _ $U $s $r) '∘ (_) _'∘> (ring_loc_intro (ascheme_mod_ring_loc $Af $r) $f $n)
↪ ring_loc_intro (ascheme_mod_ring_loc $Af (ring_mult (mod_loc_ring $Ml $U) $s $r)) (ring_mult (mod_loc_ring $Ml $U) (ring_exp (mod_loc_ring $Ml $U) $s $n) $f) $n;

And similar computations have been implemented for formal (colimits) joins D(f)∨D(g) of basic opens. But Joyal’s covering axiom D(s+r) ⊆ D(s)∪D(r) of the basic open D(s+r), has been reformulated approximately as a cover by the inclusions D(s⋅√(a⋅s + b⋅r)) ⊆ D(√(a⋅s + b⋅r)) (similarly for r) such to simultaneously also handle the unimodular (that is, ⟨r, s⟩ = 1) cover of a basic open. By the way, this functorial double-category framework is justified even for (the limit of) any  functor (diagram) of rings, rather than a single ring, because localization is left-exact …

Then, there is an implementation of locally ringed sites and schemes. But the traditional definition of schemes via isomorphisms to affine schemes won’t work computationally; instead, one has to declare that the slice-category sites of the base site satisfy the interface/specification of an affine scheme. But what is a slice-category site? How does its glue operation relate to the glue operation of the base site? This has required subtle reformulations of a continuous(-and-cocontinuous) morphism of sites with a continuous right adjoint [4] (with “technical lemma 7.20.4 00XM”):

    rule site_morph_mod_adjL $Sm $R (glue $r_)
↪ glue (adj_mod_adjL (site_morph_adj $Sm) (smod_mod $R) $r_);

But then, what is the invertibility-support D(–) for a locally ringed site and how does it relate to each affine-scheme’s invertibility-support D(–) in the slice-categories. The author of cartierSolution16.lp claims that D(f) is intended to be the SIEVE (generated by a singleton when restricted to a slice affine-scheme …) under U of all opens V where the restriction of the function f: O(U) becomes invertible, together with (a computational reformulation of) the limit condition:

    lim_{V:D(f)} O(V)  =  O(U)[1/f] 

In short, some structured data is being transferred from a base scheme to its slice-categories where they are required to satisfy the affine-scheme interface.

Moreover, the affine-scheme interface is coinductive (self-reference), meaning that its slice-categories are also required to satisfy the affine-scheme interface. This slice coinduction/self-reference is deeply intrinsic and unavoidable; so that all the constructions are always relativized (in the slice-category under an object). That is, even the affine-scheme invertibility-support D(–) constructors `ascheme_inv_slice_func`, which are the basic objects which generate the topology, are also relativized by-definition:

    constant symbol ascheme_inv_slice_func : Π [Ml : struct_mod_loc] (Af : ascheme Ml), Π [I] [U : func I (mod_loc_cat Ml)] (r : hom U (smod_mod (mod_loc_smod Ml)) (Terminal_func _)), func I (slice_cat U);

    constant symbol scheme_slice_ascheme : Π [Ml : struct_mod_loc] [Cs : struct_cov_sieve (mod_loc_site Ml)] (Sc : scheme Ml Cs), Π [U : func (cov_sieve_cat Cs) (mod_loc_cat Ml)] (u : hom U (sieve_mod (cov_sieve_hom Cs)) Id_func),
ascheme (@Struct_mod_loc (slice_cat U) (slice_site (mod_loc_site Ml) U)
  (site_morph_pullback_smod (scheme_site_morph Sc U) (mod_loc_smod Ml))
  (mod_pullb_mod_ring (mod_loc_mod_ring Ml) (slice_proj_func U))
  (mod_pullb_mod_loc (mod_loc_mod_loc Ml) (slice_proj_func U)));

A consequence of this formulation is that these various structure sheaves are now canonically related, beyond the mere usual knowledge that for any ring `R`:

    R[1/fg]  ≅   R[1/f][1/g]

MAX [5] recently defended an equivalence between functorial schemes `X` and locally-ringed-lattice schemes `Y`, approximately:

    LRDL^op( X ⇒ Spec , Y )  ≅   ( X ⇒ LRDL^op( Spec( – ), Y ) )  

where ( X ⇒ X' ) ∶= Fun( CommRing , Set )( X , X' ) and Spec: Fun(  CommRing^op, LRDL^op ). But the author of cartierSolution16.lp claims that their profunctor framework should allow a hybrid handling of schemes as locally ringed sites together with their functor-of-points semantics. And most importantly, it is not necessary to try and express those things using an internal logic (not truly-computational …) within the Zarisky topos, in the style of Thierry Coquand [6].

Ultimately, it is a conjecture that this new framework could solve the open problem of discovering a (graded) differential linear logic formulation for the algebraic-geometry’s cohomology differentials via the profunctorial semantics of linear logic in the context of sieves as profunctors…

It is also a conjecture that this new framework could solve the search of a hybrid framework⋅ combining polynomial functors (good algebra) “depending” on analytic functors (good logic) as motivated by Ehrhard’s [7, section 3.1.1, page 44] outrageous definition of the composition of polynomials by the use of differentials instead of by elementary algebra.

Another open question: would such an algebra-independent computational-logical interface for commutative (affine) schemes be able to also specify schemes of (noncommutative) associative algebras; for example, in the sense of Siqveland Arvid [8]?

But wait, here is a down-to-Earth-fresh-air sanity-check challenge (“contexte et préalables d’un débat”) for ∞-cosmonauts who may be “offended”/arguing in the vacuum against the preceding paragraphs, lol …

    https://github.com/1337777/cartier/blob/master/cartierSolution14.lp
    https://github.com/1337777/cartier/blob/master/Kosta_Dosen_2pages.pdf

where this author shows that 1+2=3 via 3 different methods: the category of natural-numbers as a higher inductive type; the natural-numbers object inside any fixed category; and the colimits inside the category of finite sets/numbers.

Indeed, this new functorial programming language, also referred as Dosen’s « m— » or « emdash » or « modos », is able to express the usual logic such as the tensor and internal-hom of profunctors, the sigma-sum and pi-product of fibred categories/profunctors; but is also able to express the concrete and inductively-constructed categories/profunctors, to express the adjunctions such as the product-and-exponential or the constant-diagram-and-limit adjunctions within any fixed category, to express contravariance and duality such as a computational-proof that right-adjoints preserve limits from the dual statement, to express groupoids and univalent universes, to express polynomial functors as bicomodules in the double category of categories, functors, cofunctors and profunctors, etc…

Such a multi-year research programme requires new tools and frameworks to articulate the speedy circulation of (papers/apps) reviews as a currency; and as for any currency, to articulate the unavoidable questions of “theft”, “falsification”, “intoxication”, “assault” beyond the traditional context of a cash-bank-robbery-by-a-gang …

An attempt at such a new platform/marketplace is this author’s « re365.net » open-source Microsoft 365 app, developed by a community of 3,000+ contributors [9], which is a tiktok-style AI-assisted calendar overlay to standardize the contacting of (VIP) researchers/businesses by reviewers whose side-goals are to co-author or by-product more intelligent (AI) interfaces for their papers/apps API.


[1] Kosta Dosen. “Cut-elimination in categories”
[9] < https://meetup.com/dubai-ai > < https://dailyReviews.link >


*/


