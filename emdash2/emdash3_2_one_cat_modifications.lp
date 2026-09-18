/* Ordinary modifications between already whole transformations.
   For OneCat(C), native component cells alpha[x] -> beta[x] are
   proposition-valued. Their remaining modification coherence is unique,
   so callers supply no additional naturality or higher-coherence field.

   The modification introduction is an explicit structural primitive beyond
   the previous Transf beta interface. Its components retain the supplied
   native cells. The identity-component path below is a derived law, staged
   to remain usable when an opposite source identity has already normalized.
   This is an ordinary-target extension; hom_int/homd_int remain the owners
   of the general directed foundation. */

require open emdash.emdash3_2;

// Structural introduction: a modification between existing whole
// transformations into a OneCat target. Point cells are proposition-valued,
// so no extra naturality or higher-coherence field is caller data.
symbol one_cat_modification [B C : Cat]
 (C1 : τ (IsNCat (cat_succ cat_zero) C))
 [F G : τ (Functor B C)] [alpha beta : τ (@Transf B C F G)]
 (m : Π x : τ (Obj B), τ (Hom (Hom_cat C (@fapp0 B C F x) (@fapp0 B C G x))
     (@tapp0_fapp0 B C F G x alpha) (@tapp0_fapp0 B C F G x beta)))
 : τ (Hom (@Transf_cat B C F G) alpha beta);


// Preserve the existing Cat-valued displayed specialization of the component.
rule @tdapp0_fapp0 _ _ _ _ _ $x
    (@one_cat_modification _ Cat_cat _ _ _ _ _ $m)
  ↪ $m $x;

// Couple the target to the constructor so the existing Cat specialization joins.
rule @tapp0_hom_fapp0 _ $C _ _ _ _ $x
    (@one_cat_modification _ $C _ _ _ _ _ $m)
  ↪ $m $x;

// Derived ordinary unit law, staged before specializing a reducible source.
// The target guard records the intended ordinary semantic qualification.
symbol one_cat_transf_identity_path [I C : Cat]
 (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (F G : τ (Functor I C)) (eta : τ (@Transf I C F G)) (x : τ (Obj I))
 : τ (@= (Hom C (@fapp0 I C F x) (@fapp0 I C G x))
     (@tapp1_fapp0 I C F G x x eta (@id I x))
     (@tapp0_fapp0 I C F G x eta))
≔ @eq_refl (Hom C (@fapp0 I C F x) (@fapp0 I C G x))
    (@tapp0_fapp0 I C F G x eta);
