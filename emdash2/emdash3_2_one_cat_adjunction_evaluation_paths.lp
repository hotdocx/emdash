/* Evaluation of whole adjunction mates through the original unit/counit formulas.
   Both targets are ordinary categories; no naturality square is caller data. */
require open emdash.emdash3_2_one_cat_adjunction_family_views;

require open emdash.emdash3_2_one_cat_adjunction_transpose_paths;

require open emdash.emdash3_2_adjunction_untranspose_naturality;

// Evaluation of the unit formula agrees with the original point transpose.
symbol one_cat_transpose_evaluation_path [K R L : Cat] (R1 : τ (IsNCat (cat_succ cat_zero) R)) (L1 : τ (IsNCat
  (cat_succ cat_zero) L))
 [F : τ (Functor R L)] [G : τ (Functor L R)] (J : τ (@Adjunction R L F G))
 (X : τ (Functor K R)) (Y : τ (Functor K L))
 (h : τ (@Transf K L (@comp_cat_fapp0 K R L F X) Y)) (x : τ (Obj K))
 : τ (@= (Hom R (@fapp0 K R X x) (@fapp0 L R G (@fapp0 K L Y x))) (@tapp0_fapp0 K R X (@comp_cat_fapp0 K L R G
  Y) x (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func K R L R1 L1 F G J X Y) h)) (@fapp0 _ _
  (@adjunction_transpose_func R L F G J (@fapp0 K R X x) (@fapp0 K L Y x)) (@tapp0_fapp0 K L (@comp_cat_fapp0 K
  R L F X) Y x h)))
≔ @eq_trans _ _ _ _
   (@eq_ap (@Transf K R X (@comp_cat_fapp0 K L R G Y)) (Hom R (@fapp0 K R X x) (@fapp0 L R G (@fapp0 K L Y x)))
  (λ m : τ (@Transf K R X (@comp_cat_fapp0 K L R G Y)), @tapp0_fapp0 K R X (@comp_cat_fapp0 K L R G Y) x m) _ _
     (@one_cat_adjunction_family_transpose_agrees K R L R1 L1 F G J X Y h))
   (@eq_sym _ _ _ (@one_cat_transpose_point_semantic_path R L R1 L1 F G J (@fapp0 K R X x) (@fapp0 K L Y x)
  (@tapp0_fapp0 K L (@comp_cat_fapp0 K R L F X) Y x h)));

// Evaluation of the counit formula agrees with the original point untranspose.
symbol one_cat_untranspose_evaluation_path [K R L : Cat] (R1 : τ (IsNCat (cat_succ cat_zero) R)) (L1 : τ (IsNCat
  (cat_succ cat_zero) L))
 [F : τ (Functor R L)] [G : τ (Functor L R)] (J : τ (@Adjunction R L F G))
 (X : τ (Functor K R)) (Y : τ (Functor K L))
 (h : τ (@Transf K R X (@comp_cat_fapp0 K L R G Y))) (x : τ (Obj K))
 : τ (@= (Hom L (@fapp0 R L F (@fapp0 K R X x)) (@fapp0 K L Y x)) (@tapp0_fapp0 K L (@comp_cat_fapp0 K R L F X)
  Y x (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func K R L R1 L1 F G J X Y) h)) (@fapp0 _ _
  (@adjunction_untranspose_func R L F G J (@fapp0 K R X x) (@fapp0 K L Y x)) (@tapp0_fapp0 K R X
  (@comp_cat_fapp0 K L R G Y) x h)))
≔ @eq_trans _ _ _ _
   (@eq_ap (@Transf K L (@comp_cat_fapp0 K R L F X) Y) (Hom L (@fapp0 R L F (@fapp0 K R X x)) (@fapp0 K L Y x))
  (λ m : τ (@Transf K L (@comp_cat_fapp0 K R L F X) Y), @tapp0_fapp0 K L (@comp_cat_fapp0 K R L F X) Y x m) _ _
     (@one_cat_adjunction_family_untranspose_agrees K R L R1 L1 F G J X Y h))
   (@eq_sym _ _ _ (@adjunction_untranspose_point_semantic_path R L F G J (@fapp0 K R X x) (@fapp0 K L Y x)
  (@tapp0_fapp0 K R X (@comp_cat_fapp0 K L R G Y) x h)));
