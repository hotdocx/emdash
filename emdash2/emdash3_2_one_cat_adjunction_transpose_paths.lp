require open emdash.emdash3_2_one_cat_adjunction_families;
require open emdash.emdash3_2_strict_transfor_component_paths;

/* Ordinary-target transpose naturality through the original unit and native mate. */

symbol one_cat_transpose_point_semantic_path
  [R L : Cat] (R1 : τ (IsNCat (cat_succ cat_zero) R)) (L1 : τ (IsNCat (cat_succ cat_zero) L))
  [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) [X : τ (Obj R)] [Y : τ (Obj L)]
  (h : τ (Hom L (@fapp0 R L F X) Y))
  : τ (@= (Hom R X (@fapp0 L R G Y))
      (@fapp0 _ _ (@adjunction_transpose_func R L F G J X Y) h)
      (@fapp0 _ _ (@adjunction_transpose_semantic_func R L F G J X Y) h))
≔ @eq_ap
    (Functor (Hom_cat L (@fapp0 R L F X) Y) (Hom_cat R X (@fapp0 L R G Y)))
    (Hom R X (@fapp0 L R G Y))
    (λ K : τ (Functor (Hom_cat L (@fapp0 R L F X) Y) (Hom_cat R X (@fapp0 L R G Y))),
      @fapp0 _ _ K h)
    _ _ (@adjunction_transpose_semantic_path R L F G J X Y);

// Postcomposition of a left mate corresponds to the right functor's whole action.
symbol one_cat_transpose_postcomp_path
  [R L : Cat] (R1 : τ (IsNCat (cat_succ cat_zero) R)) (L1 : τ (IsNCat (cat_succ cat_zero) L))
  [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) [X : τ (Obj R)] [Y0 Y1 : τ (Obj L)]
  (h : τ (Hom L (@fapp0 R L F X) Y0)) (b : τ (Hom L Y0 Y1))
  : τ (@= (Hom R X (@fapp0 L R G Y1))
      (@comp_fapp0 R X (@fapp0 L R G Y0) (@fapp0 L R G Y1)
        (@fapp1_fapp0 L R G Y0 Y1 b)
        (@fapp0 _ _ (@adjunction_transpose_func R L F G J X Y0) h))
      (@fapp0 _ _ (@adjunction_transpose_func R L F G J X Y1)
        (@comp_fapp0 L (@fapp0 R L F X) Y0 Y1 b h)))
≔ @eq_trans (Hom R X (@fapp0 L R G Y1)) _ _ _
    (@eq_ap (Hom R X (@fapp0 L R G Y0)) (Hom R X (@fapp0 L R G Y1))
      (λ k : τ (Hom R X (@fapp0 L R G Y0)), @comp_fapp0 R X (@fapp0 L R G Y0)
        (@fapp0 L R G Y1) (@fapp1_fapp0 L R G Y0 Y1 b) k)
      _ _ (@one_cat_transpose_point_semantic_path R L R1 L1 F G J X Y0 h))
    (@eq_trans (Hom R X (@fapp0 L R G Y1)) _ _ _
      (@comp_assoc R X (@fapp0 L R G (@fapp0 R L F X)) (@fapp0 L R G Y0) (@fapp0 L R G Y1)
        (@fapp1_fapp0 L R G Y0 Y1 b) (@fapp1_fapp0 L R G (@fapp0 R L F X) Y0 h)
        (@tapp0_fapp0 R R (@id_func R) (@comp_cat_fapp0 R L R G F) X (@unit_adj_transf R L F G J)))
      (@eq_sym _ _ _ (@one_cat_transpose_point_semantic_path R L R1 L1 F G J X Y1
        (@comp_fapp0 L (@fapp0 R L F X) Y0 Y1 b h))));

// Precomposition follows from the original unit's whole naturality.
symbol one_cat_transpose_precomp_path
  [R L : Cat] (R1 : τ (IsNCat (cat_succ cat_zero) R)) (L1 : τ (IsNCat (cat_succ cat_zero) L))
  [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) [X0 X1 : τ (Obj R)] [Y : τ (Obj L)]
  (a : τ (Hom R X0 X1)) (h : τ (Hom L (@fapp0 R L F X1) Y))
  : τ (@= (Hom R X0 (@fapp0 L R G Y))
      (@comp_fapp0 R X0 X1 (@fapp0 L R G Y)
        (@fapp0 _ _ (@adjunction_transpose_func R L F G J X1 Y) h) a)
      (@fapp0 _ _ (@adjunction_transpose_func R L F G J X0 Y)
        (@comp_fapp0 L (@fapp0 R L F X0) (@fapp0 R L F X1) Y h (@fapp1_fapp0 R L F X0 X1 a))))
≔ @eq_trans (Hom R X0 (@fapp0 L R G Y)) _ _ _
    (@eq_ap (Hom R X1 (@fapp0 L R G Y)) (Hom R X0 (@fapp0 L R G Y))
      (λ k : τ (Hom R X1 (@fapp0 L R G Y)), @comp_fapp0 R X0 X1 (@fapp0 L R G Y) k a)
      _ _ (@one_cat_transpose_point_semantic_path R L R1 L1 F G J X1 Y h))
    (@eq_trans (Hom R X0 (@fapp0 L R G Y)) _ _ _
      (@eq_sym _ _ _ (@comp_assoc R X0 X1 (@fapp0 L R G (@fapp0 R L F X1)) (@fapp0 L R G Y)
        (@fapp1_fapp0 L R G (@fapp0 R L F X1) Y h)
        (@tapp0_fapp0 R R (@id_func R) (@comp_cat_fapp0 R L R G F) X1 (@unit_adj_transf R L F G J)) a))
      (@eq_trans (Hom R X0 (@fapp0 L R G Y)) _ _ _
        (@eq_ap (Hom R X0 (@fapp0 L R G (@fapp0 R L F X1))) (Hom R X0 (@fapp0 L R G Y))
          (λ k : τ (Hom R X0 (@fapp0 L R G (@fapp0 R L F X1))), @comp_fapp0 R X0
            (@fapp0 L R G (@fapp0 R L F X1)) (@fapp0 L R G Y)
            (@fapp1_fapp0 L R G (@fapp0 R L F X1) Y h) k)
          _ _ (@eq_sym _ _ _ (@strict_component_naturality_path R R (@id_func R)
            (@comp_cat_fapp0 R L R G F) (@unit_adj_transf R L F G J) X0 X1 a)))
        (@eq_trans (Hom R X0 (@fapp0 L R G Y)) _ _ _
          (@comp_assoc R X0 (@fapp0 L R G (@fapp0 R L F X0)) (@fapp0 L R G (@fapp0 R L F X1))
            (@fapp0 L R G Y) (@fapp1_fapp0 L R G (@fapp0 R L F X1) Y h)
            (@fapp1_fapp0 R R (@comp_cat_fapp0 R L R G F) X0 X1 a)
            (@tapp0_fapp0 R R (@id_func R) (@comp_cat_fapp0 R L R G F) X0 (@unit_adj_transf R L F G J)))
          (@eq_sym _ _ _ (@one_cat_transpose_point_semantic_path R L R1 L1 F G J X0 Y
            (@comp_fapp0 L (@fapp0 R L F X0) (@fapp0 R L F X1) Y h (@fapp1_fapp0 R L F X0 X1 a)))))));
