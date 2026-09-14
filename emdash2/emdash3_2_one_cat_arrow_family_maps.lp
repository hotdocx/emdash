require open emdash.emdash3_2_one_cat_cokernel_family_inputs;

// Exchange the existing native whole-square action into a family of arrow diagrams.
symbol one_cat_square_family_transf [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (X0 X1 Y0 Y1 : τ
  (Functor B C)) (u : τ (@Transf B C X0 Y0)) (v : τ (@Transf B C X1 Y1)) (a : τ (@Transf B C X0 X1)) (b : τ
  (@Transf B C Y0 Y1)) (e : τ (@= (@Transf B C X0 Y1) (@comp_fapp0 (Functor_cat B C) X0 Y0 Y1 b u) (@comp_fapp0
  (Functor_cat B C) X0 X1 Y1 v a)))
 : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C X0 Y0 u)
  (@transf_arrow_diagram_func B C X1 Y1 v))
≔ @sym_func_func_transf WalkingArrow_cat B C (@walking_arrow_func (Functor_cat B C) X0 Y0 u) (@walking_arrow_func
  (Functor_cat B C) X1 Y1 v)
    (@one_cat_square_diagram_transf (Functor_cat B C) (@one_cat_functor_category B C C1)
      X0 X1 Y0 Y1 u v a b (@path_to_hom (Hom_cat (Functor_cat B C) X0 Y1) (@comp_fapp0 (Functor_cat B C) X0 Y0 Y1
  b u) (@comp_fapp0 (Functor_cat B C) X0 X1 Y1 v a) e));

// The original whole src transformation is recovered by its native shape observation.
symbol one_cat_square_family_src_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (X0 X1 Y0 Y1 : τ
  (Functor B C)) (u : τ (@Transf B C X0 Y0)) (v : τ (@Transf B C X1 Y1)) (a : τ (@Transf B C X0 X1)) (b : τ
  (@Transf B C Y0 Y1)) (e : τ (@= (@Transf B C X0 Y1) (@comp_fapp0 (Functor_cat B C) X0 Y0 Y1 b u) (@comp_fapp0
  (Functor_cat B C) X0 X1 Y1 v a)))
 : τ (@= (@Transf B C X0 X1) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C X0 Y0
  u) (@transf_arrow_diagram_func B C X1 Y1 v) (@one_cat_square_family_transf B C C1 X0 X1 Y0 Y1 u v a b e)
  walking_arrow_src) a)
≔ @eq_refl (@Transf B C X0 X1) a;

// The original whole tgt transformation is recovered by its native shape observation.
symbol one_cat_square_family_tgt_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (X0 X1 Y0 Y1 : τ
  (Functor B C)) (u : τ (@Transf B C X0 Y0)) (v : τ (@Transf B C X1 Y1)) (a : τ (@Transf B C X0 X1)) (b : τ
  (@Transf B C Y0 Y1)) (e : τ (@= (@Transf B C X0 Y1) (@comp_fapp0 (Functor_cat B C) X0 Y0 Y1 b u) (@comp_fapp0
  (Functor_cat B C) X0 X1 Y1 v a)))
 : τ (@= (@Transf B C Y0 Y1) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C X0 Y0
  u) (@transf_arrow_diagram_func B C X1 Y1 v) (@one_cat_square_family_transf B C C1 X0 X1 Y0 Y1 u v a b e)
  walking_arrow_tgt) b)
≔ @eq_refl (@Transf B C Y0 Y1) b;
