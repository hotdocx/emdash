require open emdash.emdash3_2_one_cat_modifications;
// catalog-area: Ordinary modifications and staged unit laws

// Native component evaluation retains the supplied modification component.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (F G : τ (Functor B C)) (alpha beta : τ (@Transf B C F G))
 (m : Π x : τ (Obj B), τ (Hom (Hom_cat C (@fapp0 B C F x) (@fapp0 B C G x))
     (@tapp0_fapp0 B C F G x alpha) (@tapp0_fapp0 B C F G x beta)))
 (x : τ (Obj B)) ⊢
 @tapp0_hom_fapp0 B C F G alpha beta x
   (@one_cat_modification B C C1 F G alpha beta m) ≡ m x;

// The same component computes through the public Hom action of evaluation.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (F G : τ (Functor B C)) (alpha beta : τ (@Transf B C F G))
 (m : Π x : τ (Obj B), τ (Hom (Hom_cat C (@fapp0 B C F x) (@fapp0 B C G x))
     (@tapp0_fapp0 B C F G x alpha) (@tapp0_fapp0 B C F G x beta)))
 (x : τ (Obj B)) ⊢
 @fapp1_fapp0 (@Transf_cat B C F G)
   (Hom_cat C (@fapp0 B C F x) (@fapp0 B C G x)) (@tapp0_func B C F G x) alpha beta
   (@one_cat_modification B C C1 F G alpha beta m) ≡ m x;

// No equality/reflexivity rule is installed on arbitrary whole transformations.
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (F G : τ (Functor B C)) (alpha beta : τ (@Transf B C F G)) ⊢
 @eq_refl (@Transf B C F G) alpha : τ (@= (@Transf B C F G) alpha beta);


// The staged unit law survives the normalized opposite identity presentation.
assert [A B : Cat] (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F G : τ (Functor (Op_cat A) B))
 (eta : τ (@Transf (Op_cat A) B F G)) (x : τ (Obj A)) ⊢
 @one_cat_transf_identity_path (Op_cat A) B B1 F G eta x
 : τ (@= (Hom B (@fapp0 (Op_cat A) B F x) (@fapp0 (Op_cat A) B G x))
     (@tapp1_fapp0 (Op_cat A) B F G x x eta (@id A x))
     (@tapp0_fapp0 (Op_cat A) B F G x eta));

assertnot [A B : Cat] (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F G : τ (Functor (Op_cat A) B))
 (eta : τ (@Transf (Op_cat A) B F G)) (x : τ (Obj A)) (p : τ (Hom A x x)) ⊢
 @one_cat_transf_identity_path (Op_cat A) B B1 F G eta x
 : τ (@= (Hom B (@fapp0 (Op_cat A) B F x) (@fapp0 (Op_cat A) B G x))
     (@tapp1_fapp0 (Op_cat A) B F G x x eta p)
     (@tapp0_fapp0 (Op_cat A) B F G x eta));
