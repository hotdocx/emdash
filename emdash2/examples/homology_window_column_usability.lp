/* Both expansion orders, arbitrary-arrow evaluations and non-collapse. */
require open emdash.emdash3_2_homology_window_column_usability;

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] (u : τ
    (Hom I x y)) ⊢ @homology_window_right_first_action_path I C C1 P t Ab T KP window x y u : τ (@= (Hom C (@fapp0 I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat
    C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp0 (Hom_cat I x y) (Hom_cat C (@fapp0 I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat
    C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat
    (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP
    window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) y))
    (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t
    Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window)
    y)) (@fapp1_func I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) x y)) u)
    (@fapp0 (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x y) u));

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] ⊢
    @eq_refl (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y))) (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat
    (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP
    window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) y))
    (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t
    Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window)
    y)) (@fapp1_func I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) x y)) : τ
    (@= (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y))) (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat
    (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP
    window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) y))
    (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t
    Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window)
    y)) (@fapp1_func I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) x y))
    (@fapp1_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x y));

assertnot [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] (bad : τ
    (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)))) ⊢ @eq_refl (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I
    C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat
    C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y))) (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat
    (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP
    window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) y))
    (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t
    Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window)
    y)) (@fapp1_func I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) x y)) : τ
    (@= (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y))) (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat
    (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP
    window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) y))
    (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t
    Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window)
    y)) (@fapp1_func I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) x y)) bad);

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] (u : τ
    (Hom I x y)) ⊢ @homology_window_right_diagram_action_path I C C1 P t Ab T KP window x y u : τ (@= (Hom (Functor_cat
    WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp0 (Hom_cat I x y) (Hom_cat (Functor_cat
    WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat
    (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP
    window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) y))
    (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_right_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_right_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
    (@homology_window_right_column_func I C C1 P t Ab T KP window) x y)) u) (@fapp0 (Hom_cat I x y) (Hom_cat (Functor_cat
    WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x y) u));

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] ⊢
    @eq_refl (Functor (Hom_cat I x y) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y))) (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat
    (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP
    window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) y))
    (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_right_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_right_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
    (@homology_window_right_column_func I C C1 P t Ab T KP window) x y)) : τ (@= (Functor (Hom_cat I x y) (Hom_cat
    (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y))) (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat
    (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP
    window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) y))
    (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_right_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_right_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
    (@homology_window_right_column_func I C C1 P t Ab T KP window) x y)) (@fapp1_func I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x y));

assertnot [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] (bad : τ
    (Functor (Hom_cat I x y) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)))) ⊢ @eq_refl (Functor (Hom_cat I x y) (Hom_cat (Functor_cat
    WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y))) (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat
    (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP
    window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) y))
    (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_right_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_right_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
    (@homology_window_right_column_func I C C1 P t Ab T KP window) x y)) : τ (@= (Functor (Hom_cat I x y) (Hom_cat
    (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y))) (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat
    (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP
    window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) y))
    (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_right_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_right_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
    (@homology_window_right_column_func I C C1 P t Ab T KP window) x y)) bad);

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] (u : τ
    (Hom I x y)) ⊢ @homology_window_left_first_action_path I C C1 P t Ab T KP window x y u : τ (@= (Hom C (@fapp0 I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp0
    (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t
    T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0
    I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat
    (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP
    window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP window) y))
    (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat
    C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian
    C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y))
    (@fapp1_func (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x y)) u) (@fapp0 (Hom_cat I x y) (Hom_cat C (@fapp0 I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func
    I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x y) u));

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] ⊢
    @eq_refl (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y))) (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat
    (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP
    window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP window) y))
    (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat
    C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian
    C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y))
    (@fapp1_func (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x y)) : τ (@= (Functor (Hom_cat I x y) (Hom_cat C (@fapp0
    I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)))
    (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x y)) (@fapp1_func I C (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x y));

assertnot [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] (bad : τ
    (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)))) ⊢ @eq_refl (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I
    C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C
    C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)))
    (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x y)) : τ (@= (Functor (Hom_cat I x y) (Hom_cat C (@fapp0
    I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)))
    (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x y)) bad);

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] (u : τ
    (Hom I x y)) ⊢ @homology_window_left_diagram_action_path I C C1 P t Ab T KP window x y u : τ (@= (Hom (Functor_cat
    WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp0 (Hom_cat I x y) (Hom_cat (Functor_cat
    WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat
    (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP
    window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP window) y))
    (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x y)) u) (@fapp0 (Hom_cat I x y) (Hom_cat (Functor_cat
    WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x y) u));

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] ⊢
    @eq_refl (Functor (Hom_cat I x y) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y))) (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat
    (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP
    window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP window) y))
    (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x y)) : τ (@= (Functor (Hom_cat I x y) (Hom_cat
    (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y))) (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat
    (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP
    window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP window) y))
    (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x y)) (@fapp1_func I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x y));

assertnot [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] (bad : τ
    (Functor (Hom_cat I x y) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)))) ⊢ @eq_refl (Functor (Hom_cat I x y) (Hom_cat (Functor_cat
    WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y))) (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat
    (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP
    window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP window) y))
    (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x y)) : τ (@= (Functor (Hom_cat I x y) (Hom_cat
    (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y))) (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat
    (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP
    window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP window) y))
    (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x y)) bad);
