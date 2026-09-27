/* Inverse-mate naturality from explicit whole action profiles.
   Ordinary callers derive the profiles from their existing target witness. */
require open emdash.emdash3_2_adjunction_mates;
require open emdash.emdash3_2_profile_action_paths;
require open emdash.emdash3_2_one_cat_transfor_profiles;

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
  (J : τ (@Adjunction R L F G))
  (PF : τ (@IsStrictFunctor R L F)) [X0 X1 : τ (Obj R)] [Y : τ (Obj L)]
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
      (@eq_trans _ _ _ _ (@eq_ap (Hom L (@fapp0 R L F X0) (@fapp0 R L F (@fapp0 L R G Y)))
        (Hom L (@fapp0 R L F X0) Y)
        (λ v : τ (Hom L (@fapp0 R L F X0) (@fapp0 R L F (@fapp0 L R G Y))),
          @comp_fapp0 L _ _ _ (@tapp0_fapp0 L L (@comp_cat_fapp0 L R L F G) (@id_func L) Y (@counit_adj_transf R L F G J)) v) _ _ (@eq_sym _ _ _ (@profile_composition_path R L F PF X0 X1 (@fapp0 L R G Y) h a)))
      (@eq_sym _ _ _ (@adjunction_untranspose_point_semantic_path R L F G J X0 Y
        (@comp_fapp0 R X0 X1 (@fapp0 L R G Y) h a)))));

symbol untranspose_postcomp_path
  [R L : Cat] [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G))
  (PF : τ (@IsStrictFunctor R L F)) (PE : τ (@IsStrictTransfor L L (@comp_cat_fapp0 L R L F G) (@id_func L) (@counit_adj_transf R L F G J))) [X : τ (Obj R)] [Y0 Y1 : τ (Obj L)]
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
          _ _ (@profile_component_naturality_path L L (@comp_cat_fapp0 L R L F G)
            (@id_func L) (@counit_adj_transf R L F G J) PE Y0 Y1 b))
        (@eq_trans (Hom L (@fapp0 R L F X) Y1) _ _ _
          (@eq_sym _ _ _ (@comp_assoc L
            (@fapp0 R L F X) (@fapp0 R L F (@fapp0 L R G Y0))
            (@fapp0 R L F (@fapp0 L R G Y1)) Y1
            (@tapp0_fapp0 L L (@comp_cat_fapp0 L R L F G) (@id_func L) Y1
              (@counit_adj_transf R L F G J))
            (@fapp1_fapp0 R L F (@fapp0 L R G Y0) (@fapp0 L R G Y1)
              (@fapp1_fapp0 L R G Y0 Y1 b))
            (@fapp1_fapp0 R L F X (@fapp0 L R G Y0) h)))
          (@eq_trans _ _ _ _ (@eq_ap (Hom L (@fapp0 R L F X) (@fapp0 R L F (@fapp0 L R G Y1)))
        (Hom L (@fapp0 R L F X) Y1)
        (λ v : τ (Hom L (@fapp0 R L F X) (@fapp0 R L F (@fapp0 L R G Y1))),
          @comp_fapp0 L _ _ _ (@tapp0_fapp0 L L (@comp_cat_fapp0 L R L F G) (@id_func L) Y1 (@counit_adj_transf R L F G J)) v) _ _ (@eq_sym _ _ _ (@profile_composition_path R L F PF X (@fapp0 L R G Y0) (@fapp0 L R G Y1) (@fapp1_fapp0 L R G Y0 Y1 b) h)))
      (@eq_sym _ _ _ (@adjunction_untranspose_point_semantic_path R L F G J X Y1
            (@comp_fapp0 R X _ _ (@fapp1_fapp0 L R G Y0 Y1 b) h)))))));

symbol untranspose_square_path
  [R L : Cat] [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G))
  (PF : τ (@IsStrictFunctor R L F)) (PE : τ (@IsStrictTransfor L L (@comp_cat_fapp0 L R L F G) (@id_func L) (@counit_adj_transf R L F G J))) [X0 X1 : τ (Obj R)] [Y0 Y1 : τ (Obj L)]
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
    (@untranspose_postcomp_path R L F G J PF PE X0 Y0 Y1 h0 b)
    (@eq_trans _ _ _ _
      (@eq_ap (Hom R X0 (@fapp0 L R G Y1)) (Hom L (@fapp0 R L F X0) Y1)
        (λ v : τ (Hom R X0 (@fapp0 L R G Y1)),
          @fapp0 _ _ (@adjunction_untranspose_func R L F G J X0 Y1) v)
        _ _ p)
      (@eq_sym _ _ _ (@untranspose_precomp_path R L F G J PF X0 X1 Y1 a h1)));

// Ordinary observations retain the raw functors, counit and mate maps.
symbol one_cat_untranspose_precomp_path
  [R L : Cat] (L1 : τ (IsNCat (cat_succ cat_zero) L)) [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) [X0 X1 : τ (Obj R)] [Y : τ (Obj L)]
  (a : τ (Hom R X0 X1)) (h : τ (Hom R X1 (@fapp0 L R G Y)))
  : τ (@= (Hom L (@fapp0 R L F X0) Y)
      (@comp_fapp0 L _ _ _
        (@fapp0 _ _ (@adjunction_untranspose_func R L F G J X1 Y) h)
        (@fapp1_fapp0 R L F X0 X1 a))
      (@fapp0 _ _ (@adjunction_untranspose_func R L F G J X0 Y)
        (@comp_fapp0 R X0 X1 (@fapp0 L R G Y) h a)))
≔ @untranspose_precomp_path R L F G J (@functor_into_one_cat_is_strict R L L1 F) X0 X1 Y a h;

symbol one_cat_untranspose_postcomp_path
  [R L : Cat] (L1 : τ (IsNCat (cat_succ cat_zero) L)) [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) [X : τ (Obj R)] [Y0 Y1 : τ (Obj L)]
  (h : τ (Hom R X (@fapp0 L R G Y0))) (b : τ (Hom L Y0 Y1))
  : τ (@= (Hom L (@fapp0 R L F X) Y1)
      (@comp_fapp0 L _ _ _ b
        (@fapp0 _ _ (@adjunction_untranspose_func R L F G J X Y0) h))
      (@fapp0 _ _ (@adjunction_untranspose_func R L F G J X Y1)
        (@comp_fapp0 R X _ _ (@fapp1_fapp0 L R G Y0 Y1 b) h)))
≔ @untranspose_postcomp_path R L F G J (@functor_into_one_cat_is_strict R L L1 F) (@one_cat_transfor_is_strict L L L1 (@comp_cat_fapp0 L R L F G) (@id_func L) (@counit_adj_transf R L F G J)) X Y0 Y1 h b;

symbol one_cat_untranspose_square_path
  [R L : Cat] (L1 : τ (IsNCat (cat_succ cat_zero) L)) [F : τ (Functor R L)] [G : τ (Functor L R)]
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
≔ @untranspose_square_path R L F G J (@functor_into_one_cat_is_strict R L L1 F) (@one_cat_transfor_is_strict L L L1 (@comp_cat_fapp0 L R L F G) (@id_func L) (@counit_adj_transf R L F G J)) X0 X1 Y0 Y1 a b h0 h1 p;
