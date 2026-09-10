/* Whole connecting transformation between H of the vertical columns.
   H itself is the existing whole functor. The component is the retained
   direct construction, with no cast or new choice. Generic tapp owns
   naturality and higher action; no make_transf input is required. */
require open emdash.emdash3_2_homology_window_column_usability;

/* Whole source and target of connecting: H of vertical restrictions. */
require open emdash.emdash3_2_zero_arrow_cone_homology;

symbol homology_window_source_homology_func [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T))
  : τ (Functor I C)
≔ @comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C
  P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP)
  (@homology_window_right_column_func I C C1 P t Ab T KP window);

symbol homology_window_target_homology_func [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T))
  : τ (Functor I C)
≔ @comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C
  P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP)
  (@homology_window_left_column_func I C C1 P t Ab T KP window);

/* Existing direct connecting computation at literal whole-H endpoints. */
require open emdash.emdash3_2_homology_record_connecting;
require open emdash.emdash3_2_chain_pair_homology_records;

symbol homology_window_connecting_at [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) (x : τ (Obj I))
  : τ (Hom C (@fapp0 I C (@homology_window_source_homology_func I C C1 P t Ab T KP T0 QP window) x) (@fapp0 I C
    (@homology_window_target_homology_func I C C1 P t Ab T KP T0 QP window) x))
≔ (@homology_record_connecting C P t Ab (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) (@fapp0
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
  C P t Ab) T window)) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) (@fapp0
  WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t
  T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
  Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x))
  walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) walking_arrow_tgt) (@homology_window_rowm_at I C C1 P t (@computational_abelian_preabelian C P t
  Ab) T window x) (@homology_window_row0_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T window x)
  (@homology_window_row1_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T window x) (@homology_window_row2_at I
  C C1 P t (@computational_abelian_preabelian C P t Ab) T window x) (@homology_window_F_at I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window x) (@homology_window_G_at I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window x) (@homology_window_J_at I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window x) (@homology_window_upper_zero_at I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window x) (@homology_window_lower_zero_at I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window x) (@chain_pair_homology_record C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C
  P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t
  Ab)) KP QP (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) walking_arrow_tgt) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) walking_arrow_tgt) (@fapp0 WalkingArrow_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) walking_arrow_tgt)
  (@homology_window_right_pair_at I C C1 P t Ab T KP window x)) (@chain_pair_homology_record C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C
  P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t
  Ab)) KP QP (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) x))
  (@homology_window_left_pair_at I C C1 P t Ab T KP window x)));

/* Declaration-first whole connecting transformation.
   Input coherence is retained by the actual row families and their maps.
   tapp observes the existing direct component; no naturality-square field
   or make_transf constructor is an input. */

injective symbol homology_window_connecting_transf [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T))
  : τ (@Transf I C (@homology_window_source_homology_func I C C1 P t Ab T KP T0 QP window)
    (@homology_window_target_homology_func I C C1 P t Ab T KP T0 QP window));

rule @tapp0_fapp0 _ _ _ _ $x
  (@homology_window_connecting_transf $I $C $C1 $P $t $Ab $T $KP $T0 $QP $w)
  ↪ @homology_window_connecting_at $I $C $C1 $P $t $Ab $T $KP $T0 $QP $w $x;
