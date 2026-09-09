require open emdash.emdash3_2_adjunction_mates;
require open emdash.emdash3_2_strict_transfor_component_paths;

/* Defined compatibility at the existing whole inverse-mate owner. */

symbol adjunction_untranspose_point_semantic_path
  [R L : Cat] [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) [X : τ (Obj R)] [Y : τ (Obj L)]
  (h : τ (Hom R X (@fapp0 L R G Y)))
  : τ (@= (Hom L (@fapp0 R L F X) Y)
      (@fapp0 _ _ (@adjunction_untranspose_func R L F G J X Y) h)
      (@fapp0 _ _ (@adjunction_untranspose_semantic_func R L F G J X Y) h))
≔ @eq_ap
    (Functor (Hom_cat R X (@fapp0 L R G Y)) (Hom_cat L (@fapp0 R L F X) Y))
    (Hom L (@fapp0 R L F X) Y)
    (λ U : τ (Functor (Hom_cat R X (@fapp0 L R G Y)) (Hom_cat L (@fapp0 R L F X) Y)),
      @fapp0 _ _ U h)
    (@adjunction_untranspose_func R L F G J X Y)
    (@adjunction_untranspose_semantic_func R L F G J X Y)
    (@adjunction_untranspose_semantic_path R L F G J X Y);

symbol untranspose_precomp_path
  [R L : Cat] [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) [X0 X1 : τ (Obj R)] [Y : τ (Obj L)]
  (a : τ (Hom R X0 X1)) (h : τ (Hom R X1 (@fapp0 L R G Y)))
  : τ (@= (Hom L (@fapp0 R L F X0) Y)
      (@comp_fapp0 L _ _ _
        (@fapp0 _ _ (@adjunction_untranspose_func R L F G J X1 Y) h)
        (@fapp1_fapp0 R L F X0 X1 a))
      (@fapp0 _ _ (@adjunction_untranspose_func R L F G J X0 Y)
        (@comp_fapp0 R X0 X1 (@fapp0 L R G Y) h a)))
≔ @eq_trans (Hom L (@fapp0 R L F X0) Y) _ _ _
    (@eq_ap (Hom L (@fapp0 R L F X1) Y) (Hom L (@fapp0 R L F X0) Y)
      (λ v : τ (Hom L (@fapp0 R L F X1) Y),
        @comp_fapp0 L _ _ _ v (@fapp1_fapp0 R L F X0 X1 a))
      _ _ (@adjunction_untranspose_point_semantic_path R L F G J X1 Y h))
    (@eq_trans (Hom L (@fapp0 R L F X0) Y) _ _ _
      (@eq_sym _ _ _ (@comp_assoc L
        (@fapp0 R L F X0) (@fapp0 R L F X1)
        (@fapp0 R L F (@fapp0 L R G Y)) Y
        (@tapp0_fapp0 L L (@comp_cat_fapp0 L R L F G) (@id_func L) Y
          (@counit_adj_transf R L F G J))
        (@fapp1_fapp0 R L F X1 (@fapp0 L R G Y) h)
        (@fapp1_fapp0 R L F X0 X1 a)))
      (@eq_sym _ _ _ (@adjunction_untranspose_point_semantic_path R L F G J X0 Y
        (@comp_fapp0 R X0 X1 (@fapp0 L R G Y) h a))));

/* Postcomposition of inverse mates, from the actual counit naturality. */

symbol untranspose_postcomp_path
  [R L : Cat] [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) [X : τ (Obj R)] [Y0 Y1 : τ (Obj L)]
  (h : τ (Hom R X (@fapp0 L R G Y0))) (b : τ (Hom L Y0 Y1))
  : τ (@= (Hom L (@fapp0 R L F X) Y1)
      (@comp_fapp0 L _ _ _ b
        (@fapp0 _ _ (@adjunction_untranspose_func R L F G J X Y0) h))
      (@fapp0 _ _ (@adjunction_untranspose_func R L F G J X Y1)
        (@comp_fapp0 R X _ _ (@fapp1_fapp0 L R G Y0 Y1 b) h)))
≔ @eq_trans (Hom L (@fapp0 R L F X) Y1) _ _ _
    (@eq_ap (Hom L (@fapp0 R L F X) Y0) (Hom L (@fapp0 R L F X) Y1)
      (λ v : τ (Hom L (@fapp0 R L F X) Y0), @comp_fapp0 L _ _ _ b v)
      _ _ (@adjunction_untranspose_point_semantic_path R L F G J X Y0 h))
    (@eq_trans (Hom L (@fapp0 R L F X) Y1) _ _ _
      (@comp_assoc L (@fapp0 R L F X) (@fapp0 R L F (@fapp0 L R G Y0)) Y0 Y1
        b (@tapp0_fapp0 L L (@comp_cat_fapp0 L R L F G) (@id_func L) Y0
          (@counit_adj_transf R L F G J))
        (@fapp1_fapp0 R L F X (@fapp0 L R G Y0) h))
      (@eq_trans (Hom L (@fapp0 R L F X) Y1) _ _ _
        (@eq_ap (Hom L (@fapp0 R L F (@fapp0 L R G Y0)) Y1)
          (Hom L (@fapp0 R L F X) Y1)
          (λ v : τ (Hom L (@fapp0 R L F (@fapp0 L R G Y0)) Y1),
            @comp_fapp0 L _ _ _ v (@fapp1_fapp0 R L F X (@fapp0 L R G Y0) h))
          _ _ (@strict_component_naturality_path L L (@comp_cat_fapp0 L R L F G)
            (@id_func L) (@counit_adj_transf R L F G J) Y0 Y1 b))
        (@eq_trans (Hom L (@fapp0 R L F X) Y1) _ _ _
          (@eq_sym _ _ _ (@comp_assoc L
            (@fapp0 R L F X) (@fapp0 R L F (@fapp0 L R G Y0))
            (@fapp0 R L F (@fapp0 L R G Y1)) Y1
            (@tapp0_fapp0 L L (@comp_cat_fapp0 L R L F G) (@id_func L) Y1
              (@counit_adj_transf R L F G J))
            (@fapp1_fapp0 R L F (@fapp0 L R G Y0) (@fapp0 L R G Y1)
              (@fapp1_fapp0 L R G Y0 Y1 b))
            (@fapp1_fapp0 R L F X (@fapp0 L R G Y0) h)))
          (@eq_sym _ _ _ (@adjunction_untranspose_point_semantic_path R L F G J X Y1
            (@comp_fapp0 R X _ _ (@fapp1_fapp0 L R G Y0 Y1 b) h))))));

/* A compatible square on right mates yields the corresponding left square. */

symbol untranspose_square_path
  [R L : Cat] [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) [X0 X1 : τ (Obj R)] [Y0 Y1 : τ (Obj L)]
  (a : τ (Hom R X0 X1)) (b : τ (Hom L Y0 Y1))
  (h0 : τ (Hom R X0 (@fapp0 L R G Y0)))
  (h1 : τ (Hom R X1 (@fapp0 L R G Y1)))
  (p : τ (@= (Hom R X0 (@fapp0 L R G Y1))
    (@comp_fapp0 R X0 _ _ (@fapp1_fapp0 L R G Y0 Y1 b) h0)
    (@comp_fapp0 R X0 X1 _ h1 a)))
  : τ (@= (Hom L (@fapp0 R L F X0) Y1)
      (@comp_fapp0 L _ _ _ b
        (@fapp0 _ _ (@adjunction_untranspose_func R L F G J X0 Y0) h0))
      (@comp_fapp0 L _ _ _
        (@fapp0 _ _ (@adjunction_untranspose_func R L F G J X1 Y1) h1)
        (@fapp1_fapp0 R L F X0 X1 a)))
≔ @eq_trans _ _ _ _
    (@untranspose_postcomp_path R L F G J X0 Y0 Y1 h0 b)
    (@eq_trans _ _ _ _
      (@eq_ap (Hom R X0 (@fapp0 L R G Y1)) (Hom L (@fapp0 R L F X0) Y1)
        (λ v : τ (Hom R X0 (@fapp0 L R G Y1)),
          @fapp0 _ _ (@adjunction_untranspose_func R L F G J X0 Y1) v)
        _ _ p)
      (@eq_sym _ _ _ (@untranspose_precomp_path R L F G J X0 X1 Y1 a h1)));
