/* Whole/component/Hom-action qualification of connecting. */
require open emdash.emdash3_2_homology_window_connecting_transformation;

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) (x : τ (Obj I)) ⊢
  @fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) x ≡
    @homology_window_right_column_at I C C1 P t Ab T KP window x;

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] ⊢
  @fapp1_func I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) x y : τ (Functor
    (Hom_cat I x y)
    (Hom_cat (@ZeroArrowCone_cat C t T) (@homology_window_right_column_at I C C1 P t Ab T KP window x)
      (@homology_window_right_column_at I C C1 P t Ab T KP window y)));

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) (x : τ (Obj I)) ⊢
  @fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP window) x ≡
    @homology_window_left_column_at I C C1 P t Ab T KP window x;

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] ⊢
  @fapp1_func I (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP window) x y : τ (Functor
    (Hom_cat I x y)
    (Hom_cat (@ZeroArrowCone_cat C t T) (@homology_window_left_column_at I C C1 P t Ab T KP window x)
      (@homology_window_left_column_at I C C1 P t Ab T KP window y)));

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) ⊢
    (@homology_window_connecting_transf I C C1 P t Ab T KP T0 QP window) : τ (@Transf I C
    (@homology_window_source_homology_func I C C1 P t Ab T KP T0 QP window) (@homology_window_target_homology_func I C C1 P
    t Ab T KP T0 QP window));

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) (x : τ (Obj I)) ⊢
  @tapp0_fapp0 I C (@homology_window_source_homology_func I C C1 P t Ab T KP T0 QP window)
    (@homology_window_target_homology_func I C C1 P t Ab T KP T0 QP window) x (@homology_window_connecting_transf I C C1 P t
    Ab T KP T0 QP window) ≡ (@homology_window_connecting_at I C C1 P t Ab T KP T0 QP window x);

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] ⊢
    (@tapp1_func I C (@homology_window_source_homology_func I C C1 P t Ab T KP T0 QP window)
    (@homology_window_target_homology_func I C C1 P t Ab T KP T0 QP window) x y (@homology_window_connecting_transf I C C1 P
    t Ab T KP T0 QP window))
  : τ (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@homology_window_source_homology_func I C C1 P t Ab T KP T0 QP
    window) x) (@fapp0 I C (@homology_window_target_homology_func I C C1 P t Ab T KP T0 QP window) y)));

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] (u : τ
    (Hom I x y)) ⊢
  @fapp0 (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@homology_window_source_homology_func I C C1 P t Ab T KP T0 QP window) x)
    (@fapp0 I C (@homology_window_target_homology_func I C C1 P t Ab T KP T0 QP window) y)) (@tapp1_func I C
    (@homology_window_source_homology_func I C C1 P t Ab T KP T0 QP window) (@homology_window_target_homology_func I C C1 P
    t Ab T KP T0 QP window) x y (@homology_window_connecting_transf I C C1 P t Ab T KP T0 QP window)) u
  ≡ @tapp1_fapp0 I C (@homology_window_source_homology_func I C C1 P t Ab T KP T0 QP window)
    (@homology_window_target_homology_func I C C1 P t Ab T KP T0 QP window) x y (@homology_window_connecting_transf I C C1 P
    t Ab T KP T0 QP window) u;

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] (u v : τ
    (Hom I x y)) ⊢
  @fapp1_func (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@homology_window_source_homology_func I C C1 P t Ab T KP T0 QP window)
    x) (@fapp0 I C (@homology_window_target_homology_func I C C1 P t Ab T KP T0 QP window) y)) (@tapp1_func I C
    (@homology_window_source_homology_func I C C1 P t Ab T KP T0 QP window) (@homology_window_target_homology_func I C C1 P
    t Ab T KP T0 QP window) x y (@homology_window_connecting_transf I C C1 P t Ab T KP T0 QP window)) u v
  : τ (Functor (Hom_cat (Hom_cat I x y) u v)
    (Hom_cat (Hom_cat C (@fapp0 I C (@homology_window_source_homology_func I C C1 P t Ab T KP T0 QP window) x) (@fapp0 I C
      (@homology_window_target_homology_func I C C1 P t Ab T KP T0 QP window) y))
      (@tapp1_fapp0 I C (@homology_window_source_homology_func I C C1 P t Ab T KP T0 QP window)
        (@homology_window_target_homology_func I C C1 P t Ab T KP T0 QP window) x y (@homology_window_connecting_transf I C
        C1 P t Ab T KP T0 QP window) u)
      (@tapp1_fapp0 I C (@homology_window_source_homology_func I C C1 P t Ab T KP T0 QP window)
        (@homology_window_target_homology_func I C C1 P t Ab T KP T0 QP window) x y (@homology_window_connecting_transf I C
        C1 P t Ab T KP T0 QP window) v)));

/* Observations as whole functors, retaining all their actions. */
require open emdash.emdash3_2_homology_window_columns;

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) ⊢ (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@homology_window_right_column_func I C C1 P t Ab T KP
    window)) ≡ (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)));

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) ⊢ (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T)
    (@homology_window_right_column_func I C C1 P t Ab T KP window)) ≡ (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I
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
    (@computational_abelian_preabelian C P t Ab) T window)));

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) ⊢ (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@homology_window_left_column_func I C C1 P t Ab T KP
    window)) ≡ (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)));

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) ⊢ (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window)) ≡ (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I
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
    (@computational_abelian_preabelian C P t Ab) T window)));
