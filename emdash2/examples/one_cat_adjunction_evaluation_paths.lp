/* The same mate-evaluation paths remain usable after arbitrary postcomposition. */
require open emdash.emdash3_2_one_cat_adjunction_evaluation_paths;

assert [K R L : Cat] (R1 : τ (IsNCat (cat_succ cat_zero) R)) (L1 : τ (IsNCat
  (cat_succ cat_zero) L))
 [F : τ (Functor R L)] [G : τ (Functor L R)] (J : τ (@Adjunction R L F G))
 (X : τ (Functor K R)) (Y : τ (Functor K L))
 (h : τ (@Transf K L (@comp_cat_fapp0 K R L F X) Y)) (x : τ (Obj K))
  (W : τ (Obj R)) (after : τ (Hom R (@fapp0 L R G (@fapp0 K L Y x)) W))
 ⊢ (@eq_ap (Hom R (@fapp0 K R X x) (@fapp0 L R G (@fapp0 K L Y x))) (Hom R (@fapp0 K R X x) W) (λ q : τ (Hom R
  (@fapp0 K R X x) (@fapp0 L R G (@fapp0 K L Y x))), @comp_fapp0 R (@fapp0 K R X x) (@fapp0 L R G (@fapp0 K L Y
  x)) W after q) (@tapp0_fapp0 K R X (@comp_cat_fapp0 K L R G
  Y) x (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func K R L R1 L1 F G J X Y) h)) (@fapp0 _ _
  (@adjunction_transpose_func R L F G J (@fapp0 K R X x) (@fapp0 K L Y x)) (@tapp0_fapp0 K L (@comp_cat_fapp0 K
  R L F X) Y x h)) (@one_cat_transpose_evaluation_path K R L R1 L1 F G J X Y h x)) : τ (@= (Hom R (@fapp0 K R X
  x) W) (@comp_fapp0 R (@fapp0 K R X x) (@fapp0 L R G (@fapp0 K L Y x)) W after (@tapp0_fapp0 K R X
  (@comp_cat_fapp0 K L R G
  Y) x (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func K R L R1 L1 F G J X Y) h))) (@comp_fapp0 R (@fapp0
  K R X x) (@fapp0 L R G (@fapp0 K L Y x)) W after (@fapp0 _ _
  (@adjunction_transpose_func R L F G J (@fapp0 K R X x) (@fapp0 K L Y x)) (@tapp0_fapp0 K L (@comp_cat_fapp0 K
  R L F X) Y x h))));

assert [K R L : Cat] (R1 : τ (IsNCat (cat_succ cat_zero) R)) (L1 : τ (IsNCat
  (cat_succ cat_zero) L))
 [F : τ (Functor R L)] [G : τ (Functor L R)] (J : τ (@Adjunction R L F G))
 (X : τ (Functor K R)) (Y : τ (Functor K L))
 (h : τ (@Transf K R X (@comp_cat_fapp0 K L R G Y))) (x : τ (Obj K))
  (W : τ (Obj L)) (after : τ (Hom L (@fapp0 K L Y x) W))
 ⊢ (@eq_ap (Hom L (@fapp0 R L F (@fapp0 K R X x)) (@fapp0 K L Y x)) (Hom L (@fapp0 R L F (@fapp0 K R X x)) W) (λ
  q : τ (Hom L (@fapp0 R L F (@fapp0 K R X x)) (@fapp0 K L Y x)), @comp_fapp0 L (@fapp0 R L F (@fapp0 K R X x))
  (@fapp0 K L Y x) W after q) (@tapp0_fapp0 K L (@comp_cat_fapp0 K R L F X)
  Y x (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func K R L R1 L1 F G J X Y) h)) (@fapp0 _ _
  (@adjunction_untranspose_func R L F G J (@fapp0 K R X x) (@fapp0 K L Y x)) (@tapp0_fapp0 K R X
  (@comp_cat_fapp0 K L R G Y) x h)) (@one_cat_untranspose_evaluation_path K R L R1 L1 F G J X Y h x)) : τ (@=
  (Hom L (@fapp0 R L F (@fapp0 K R X x)) W) (@comp_fapp0 L (@fapp0 R L F (@fapp0 K R X x)) (@fapp0 K L Y x) W
  after (@tapp0_fapp0 K L (@comp_cat_fapp0 K R L F X)
  Y x (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func K R L R1 L1 F G J X Y) h))) (@comp_fapp0 L
  (@fapp0 R L F (@fapp0 K R X x)) (@fapp0 K L Y x) W after (@fapp0 _ _
  (@adjunction_untranspose_func R L F G J (@fapp0 K R X x) (@fapp0 K L Y x)) (@tapp0_fapp0 K R X
  (@comp_cat_fapp0 K L R G Y) x h))));
