/* Vertical column restrictions, retaining the selected native inputs. */
require open emdash.emdash3_2_homology_window_families;

/* Vertical column windows, retaining the original row observations. */
require open emdash.emdash3_2_homology_connecting_left_lift;
require open emdash.emdash3_2_short_exact_row_chain_columns;
require open emdash.emdash3_2_short_exact_row_chain_projection;
require open emdash.emdash3_2_chain_pair_zero_cones;

// The source uses the SAME right-step pair as the connecting construction.
symbol homology_window_right_pair_at [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) (x : τ (Obj I))
  : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) x)) walking_arrow_tgt) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) walking_arrow_tgt)
    (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) x)) walking_arrow_tgt))
≔ (@homology_connecting_step_right_pair C P t Ab (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) (@fapp0
  WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t
  T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
  Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x))
  walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) (@fapp0
  WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t
  T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
  Ab) T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x))
  walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) walking_arrow_tgt) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) walking_arrow_tgt) (@homology_window_row0_at I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window x) (@homology_window_row1_at I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window x) (@homology_window_G_at I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window x) (@computational_chain_pair_map_prev C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@fapp0 (@ZeroArrowCone_cat C t
  T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) walking_arrow_tgt) (@computational_short_exact_row_pair
  C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t
  T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
  Ab) T (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) (@fapp0
  WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t
  T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
  Ab) T (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x))
  walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) walking_arrow_tgt) (@homology_window_rowm_at I C C1 P t (@computational_abelian_preabelian C P t
  Ab) T window x)) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat
  C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) walking_arrow_tgt)
  (@homology_window_row0_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T window x)) (@homology_window_F_at I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window x)) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) (@fapp0
  WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t
  T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
  Ab) T (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x))
  walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) (@fapp0
  WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t
  T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
  Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x))
  walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) (@fapp0
  WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t
  T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
  Ab) T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x))
  walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) walking_arrow_tgt) (@homology_window_rowm_at I C C1 P t (@computational_abelian_preabelian C P t
  Ab) T window x) (@homology_window_row0_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T window x)
  (@homology_window_row1_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T window x) (@homology_window_F_at I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window x) (@homology_window_G_at I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window x) (@homology_window_upper_zero_at I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window x)));

// The shifted left column uses the original derived left chain law.
symbol homology_window_left_pair_at [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) (x : τ (Obj I))
  : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window)) x)))
≔ (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T)
  C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) walking_arrow_tgt) (@homology_window_row0_at I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window x) (@homology_window_row1_at I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window x) (@homology_window_row2_at I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window x) (@homology_window_G_at I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window x) (@homology_window_J_at I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window x) (@homology_window_lower_zero_at I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window x));

symbol homology_window_right_column_at [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) (x : τ (Obj I))
  : τ (Obj (@ZeroArrowCone_cat C t T))
≔ (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
  (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP (@fapp0 WalkingArrow_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) walking_arrow_tgt)
  (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) walking_arrow_tgt) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) walking_arrow_tgt) (@homology_window_right_pair_at I C
  C1 P t Ab T KP window x));

symbol homology_window_left_column_at [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) (x : τ (Obj I))
  : τ (Obj (@ZeroArrowCone_cat C t T))
≔ (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
  (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) (@homology_window_left_pair_at I C C1 P t Ab T KP
  window x));

/* Whole column restrictions. Their components retain the original native
   inputs; whole Hom actions remain owned by generic fapp. */

// The right column of a coherent short-exact window, not horizontal row H.
injective symbol homology_window_right_column_func [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T))
  : τ (Functor I (@ZeroArrowCone_cat C t T));

rule @fapp0 _ _
  (@homology_window_right_column_func $I $C $C1 $P $t $Ab $T $KP $w) $x
  ↪ @homology_window_right_column_at $I $C $C1 $P $t $Ab $T $KP $w $x;

// The left column of a coherent short-exact window, not horizontal row H.
injective symbol homology_window_left_column_func [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T))
  : τ (Functor I (@ZeroArrowCone_cat C t T));

rule @fapp0 _ _
  (@homology_window_left_column_func $I $C $C1 $P $t $Ab $T $KP $w) $x
  ↪ @homology_window_left_column_at $I $C $C1 $P $t $Ab $T $KP $w $x;

/* Whole structural observations of the selected vertical columns.
   Patterns use the actual primitive heads of the existing native comma
   projections; all endpoint expressions are inferred. */
require open emdash.emdash3_2_arrow_diagram_families;

// Native first projection followed by the right column.
rule @comp_fapp0 Cat_cat _ _ _
  (@Op_func _ _ (@Sigma_proj1_func _ _))
  (@homology_window_right_column_func $I $C $C1 $P $t $Ab $T _ $window)
  ↪ (@comp_cat_fapp0 $I (@ZeroArrowCone_cat $C $t $T) $C (@zero_arrow_cone_vertex_func $C $t $T walking_arrow_tgt)
    (@short_exact_row_family_func $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T
    (@homology_window_family_rowm $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T $window)));

// Native second projection, after Op/composition expose its two factors.
// lhs-audit: keep 4 -- SR cannot recover the arrow-diagram target from the
// nested native Sigma projection alone. Functor_cat is the surviving head;
// Hom_cat Cat_cat would reduce away before this pattern can discriminate.
rule @comp_fapp0 Cat_cat _ _ (@Functor_cat (@Join_cat Terminal_cat Terminal_cat) $C)
  (@comp_fapp0 Cat_cat _ _ _
    (@Op_func _ _ (@Product_projR_func _ _))
    (@Op_func _ _ (@sigma_map_func _ _ _
      (@Op_funcd _ _ _ (@sigma_proj1_family_funcd _ _ _)))))
  (@homology_window_right_column_func $I $C $C1 $P $t $Ab $T _ $window)
  ↪ (@transf_arrow_diagram_func $I $C (@comp_cat_fapp0 $I (@ZeroArrowCone_cat $C $t $T) $C (@zero_arrow_cone_vertex_func $C
    $t $T walking_arrow_tgt) (@short_exact_row_family_func $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab)
    $T (@homology_window_family_row0 $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T $window)))
    (@comp_cat_fapp0 $I (@ZeroArrowCone_cat $C $t $T) $C (@zero_arrow_cone_vertex_func $C $t $T walking_arrow_tgt)
    (@short_exact_row_family_func $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T
    (@homology_window_family_row1 $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T $window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func $I (@ZeroArrowCone_cat $C $t $T) $C (@zero_arrow_cone_vertex_func $C $t $T walking_arrow_tgt)
    (@short_exact_row_family_func $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T
    (@homology_window_family_row0 $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T $window))
    (@short_exact_row_family_func $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T
    (@homology_window_family_row1 $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T $window)))
    (@homology_window_family_G $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T $window)));

// Native first projection followed by the left column.
rule @comp_fapp0 Cat_cat _ _ _
  (@Op_func _ _ (@Sigma_proj1_func _ _))
  (@homology_window_left_column_func $I $C $C1 $P $t $Ab $T _ $window)
  ↪ (@comp_cat_fapp0 $I (@ZeroArrowCone_cat $C $t $T) $C (@zero_arrow_cone_first_func $C $t $T)
    (@short_exact_row_family_func $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T
    (@homology_window_family_row0 $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T $window)));

// Native second projection, after Op/composition expose its two factors.
// lhs-audit: keep 4 -- same measured arrow-diagram target reconstruction guard.
rule @comp_fapp0 Cat_cat _ _ (@Functor_cat (@Join_cat Terminal_cat Terminal_cat) $C)
  (@comp_fapp0 Cat_cat _ _ _
    (@Op_func _ _ (@Product_projR_func _ _))
    (@Op_func _ _ (@sigma_map_func _ _ _
      (@Op_funcd _ _ _ (@sigma_proj1_family_funcd _ _ _)))))
  (@homology_window_left_column_func $I $C $C1 $P $t $Ab $T _ $window)
  ↪ (@transf_arrow_diagram_func $I $C (@comp_cat_fapp0 $I (@ZeroArrowCone_cat $C $t $T) $C (@zero_arrow_cone_first_func $C
    $t $T) (@short_exact_row_family_func $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T
    (@homology_window_family_row1 $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T $window)))
    (@comp_cat_fapp0 $I (@ZeroArrowCone_cat $C $t $T) $C (@zero_arrow_cone_first_func $C $t $T)
    (@short_exact_row_family_func $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T
    (@homology_window_family_row2 $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T $window))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func $I (@ZeroArrowCone_cat $C $t $T) $C (@zero_arrow_cone_first_func $C $t $T)
    (@short_exact_row_family_func $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T
    (@homology_window_family_row1 $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T $window))
    (@short_exact_row_family_func $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T
    (@homology_window_family_row2 $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T $window)))
    (@homology_window_family_J $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T $window)));
