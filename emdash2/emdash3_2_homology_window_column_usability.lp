/* Hom-action usability for the whole column observations.
   Generic action may expand a composite before the whole observation folds.
   These four narrow proof-time rules compare that expanded form with the
   original row action. They do not replace generic runtime action or
   reverse arbitrary directed cells. Endpoint/frame constraints are on the
   RHS, while the LHS discriminates on surviving primitive owners. */
require open emdash.emdash3_2_homology_window_columns;

unif_rule
  @comp_fapp0 Cat_cat _ _ _
    (@fapp1_func _ _ (@Sigma_proj1_func $K $E) _ _)
    (@fapp1_func _ _ (@homology_window_right_column_func $I $C $C1 $P $t $Ab $T _ $window) $x $y)
  ≡ @comp_fapp0 Cat_cat _ _ _ $outer $inner
  ↪ [ $K ≡ Op_cat $C; $E ≡ (@homdc_op_edge_catd $C (Functor_cat WalkingArrow_cat $C) (@represented_comma_prof $C
    (Functor_cat WalkingArrow_cat $C) (@terminal_arrow_diagram_func $C $t $T)));
      $outer ≡ (@fapp1_func (@ZeroArrowCone_cat $C $t $T) $C (@zero_arrow_cone_vertex_func $C $t $T walking_arrow_tgt)
        (@fapp0 $I (@ZeroArrowCone_cat $C $t $T) (@short_exact_row_family_func $I $C $C1 $P $t
        (@computational_abelian_preabelian $C $P $t $Ab) $T (@homology_window_family_rowm $I $C $C1 $P $t
        (@computational_abelian_preabelian $C $P $t $Ab) $T $window)) $x) (@fapp0 $I (@ZeroArrowCone_cat $C $t $T)
        (@short_exact_row_family_func $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T
        (@homology_window_family_rowm $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T $window)) $y));
      $inner ≡ (@fapp1_func $I (@ZeroArrowCone_cat $C $t $T) (@short_exact_row_family_func $I $C $C1 $P $t
        (@computational_abelian_preabelian $C $P $t $Ab) $T (@homology_window_family_rowm $I $C $C1 $P $t
        (@computational_abelian_preabelian $C $P $t $Ab) $T $window)) $x $y) ];

unif_rule
  @comp_fapp0 Cat_cat _ _ _
    (@fapp1_func _ _ (@Sigma_proj1_func $K $E) _ _)
    (@fapp1_func _ _ (@homology_window_left_column_func $I $C $C1 $P $t $Ab $T _ $window) $x $y)
  ≡ @comp_fapp0 Cat_cat _ _ _ $outer $inner
  ↪ [ $K ≡ Op_cat $C; $E ≡ (@homdc_op_edge_catd $C (Functor_cat WalkingArrow_cat $C) (@represented_comma_prof $C
    (Functor_cat WalkingArrow_cat $C) (@terminal_arrow_diagram_func $C $t $T)));
      $outer ≡ (@fapp1_func (@Sigma_cat (Op_cat $C) $E) (Op_cat $C)
        (@Sigma_proj1_func (Op_cat $C) $E) (@fapp0 $I (@ZeroArrowCone_cat $C $t $T) (@short_exact_row_family_func $I $C $C1
          $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T (@homology_window_family_row0 $I $C $C1 $P $t
          (@computational_abelian_preabelian $C $P $t $Ab) $T $window)) $y) (@fapp0 $I (@ZeroArrowCone_cat $C $t $T)
          (@short_exact_row_family_func $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T
          (@homology_window_family_row0 $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T $window)) $x));
      $inner ≡ (@fapp1_func $I (@ZeroArrowCone_cat $C $t $T) (@short_exact_row_family_func $I $C $C1 $P $t
        (@computational_abelian_preabelian $C $P $t $Ab) $T (@homology_window_family_row0 $I $C $C1 $P $t
        (@computational_abelian_preabelian $C $P $t $Ab) $T $window)) $x $y) ];

unif_rule
  @comp_fapp0 Cat_cat _ _ _
    (@comp_fapp0 Cat_cat _ _ _
      (@Product_projR_func _ _)
      (@Op_func _ _ (@sigma_map_func _ _ _
        (@fdapp1_int_presheaf_arrow _ _ _
          (@Op_funcd _ _ _ (@sigma_proj1_family_funcd $K $D $G))
          $a $u $b $v))))
    (@fapp1_func _ _ (@homology_window_right_column_func $I $C $C1 $P $t $Ab $T $KP $window) $x $y)
  ≡ @sym_fapp1_func $A0 $B0 $C0 $H $x0 $y0
  ↪ [ $K ≡ Op_cat $C; $D ≡ Functor_cat WalkingArrow_cat $C; $G ≡ (@represented_comma_prof $C (Functor_cat WalkingArrow_cat
    $C) (@terminal_arrow_diagram_func $C $t $T));
      $a ≡ sigma_Fst (@homology_window_right_column_at $I $C $C1 $P $t $Ab $T $KP $window $y); $u ≡ sigma_Snd
        (@homology_window_right_column_at $I $C $C1 $P $t $Ab $T $KP $window $y);
      $b ≡ sigma_Fst (@homology_window_right_column_at $I $C $C1 $P $t $Ab $T $KP $window $x); $v ≡ sigma_Snd
        (@homology_window_right_column_at $I $C $C1 $P $t $Ab $T $KP $window $x);
      $A0 ≡ WalkingArrow_cat; $B0 ≡ $I; $C0 ≡ $C;
      $H ≡ (@walking_arrow_func (Functor_cat $I $C) (@comp_cat_fapp0 $I (@ZeroArrowCone_cat $C $t $T) $C
        (@zero_arrow_cone_vertex_func $C $t $T walking_arrow_tgt) (@short_exact_row_family_func $I $C $C1 $P $t
        (@computational_abelian_preabelian $C $P $t $Ab) $T (@homology_window_family_row0 $I $C $C1 $P $t
        (@computational_abelian_preabelian $C $P $t $Ab) $T $window))) (@comp_cat_fapp0 $I (@ZeroArrowCone_cat $C $t $T) $C
        (@zero_arrow_cone_vertex_func $C $t $T walking_arrow_tgt) (@short_exact_row_family_func $I $C $C1 $P $t
        (@computational_abelian_preabelian $C $P $t $Ab) $T (@homology_window_family_row1 $I $C $C1 $P $t
        (@computational_abelian_preabelian $C $P $t $Ab) $T $window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func $I
        (@ZeroArrowCone_cat $C $t $T) $C (@zero_arrow_cone_vertex_func $C $t $T walking_arrow_tgt)
        (@short_exact_row_family_func $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T
        (@homology_window_family_row0 $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T $window))
        (@short_exact_row_family_func $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T
        (@homology_window_family_row1 $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T $window)))
        (@homology_window_family_G $I $C $C1 $P $t (@computational_abelian_preabelian $C $P $t $Ab) $T $window))); $x0 ≡ $x;
        $y0 ≡ $y ];

unif_rule
  @comp_fapp0 Cat_cat _ _ _
    (@comp_fapp0 Cat_cat _ _ _
      (@Product_projR_func _ _)
      (@Op_func _ _ (@sigma_map_func _ _ _
        (@fdapp1_int_presheaf_arrow _ _ _
          (@Op_funcd _ _ _ (@sigma_proj1_family_funcd $K $D $G))
          $a $u $b $v))))
    (@fapp1_func _ _ (@homology_window_left_column_func $I $C $C1 $P $t $Ab $T $KP $window) $x $y)
  ≡ @sym_fapp1_func $A0 $B0 $C0 $H $x0 $y0
  ↪ [ $K ≡ Op_cat $C; $D ≡ Functor_cat WalkingArrow_cat $C; $G ≡ (@represented_comma_prof $C (Functor_cat WalkingArrow_cat
    $C) (@terminal_arrow_diagram_func $C $t $T));
      $a ≡ sigma_Fst (@homology_window_left_column_at $I $C $C1 $P $t $Ab $T $KP $window $y); $u ≡ sigma_Snd
        (@homology_window_left_column_at $I $C $C1 $P $t $Ab $T $KP $window $y);
      $b ≡ sigma_Fst (@homology_window_left_column_at $I $C $C1 $P $t $Ab $T $KP $window $x); $v ≡ sigma_Snd
        (@homology_window_left_column_at $I $C $C1 $P $t $Ab $T $KP $window $x);
      $A0 ≡ WalkingArrow_cat; $B0 ≡ $I; $C0 ≡ $C;
      $H ≡ (@walking_arrow_func (Functor_cat $I $C) (@comp_cat_fapp0 $I (@ZeroArrowCone_cat $C $t $T) $C
        (@zero_arrow_cone_first_func $C $t $T) (@short_exact_row_family_func $I $C $C1 $P $t
        (@computational_abelian_preabelian $C $P $t $Ab) $T (@homology_window_family_row1 $I $C $C1 $P $t
        (@computational_abelian_preabelian $C $P $t $Ab) $T $window))) (@comp_cat_fapp0 $I (@ZeroArrowCone_cat $C $t $T) $C
        (@zero_arrow_cone_first_func $C $t $T) (@short_exact_row_family_func $I $C $C1 $P $t
        (@computational_abelian_preabelian $C $P $t $Ab) $T (@homology_window_family_row2 $I $C $C1 $P $t
        (@computational_abelian_preabelian $C $P $t $Ab) $T $window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func $I
        (@ZeroArrowCone_cat $C $t $T) $C (@zero_arrow_cone_first_func $C $t $T) (@short_exact_row_family_func $I $C $C1 $P
        $t (@computational_abelian_preabelian $C $P $t $Ab) $T (@homology_window_family_row1 $I $C $C1 $P $t
        (@computational_abelian_preabelian $C $P $t $Ab) $T $window)) (@short_exact_row_family_func $I $C $C1 $P $t
        (@computational_abelian_preabelian $C $P $t $Ab) $T (@homology_window_family_row2 $I $C $C1 $P $t
        (@computational_abelian_preabelian $C $P $t $Ab) $T $window))) (@homology_window_family_J $I $C $C1 $P $t
        (@computational_abelian_preabelian $C $P $t $Ab) $T $window))); $x0 ≡ $x; $y0 ≡ $y ];

/* Expanded first Hom-action comparison with the selected usability rule. */

symbol homology_window_right_first_hom_whole_path [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)]
  : τ (@= (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y))) (@fapp1_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C
    t T) C (@zero_arrow_cone_first_func C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window)) x y)
    (@fapp1_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x y))
≔ @eq_refl (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
  walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y))) (@fapp1_func I C
  (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@homology_window_right_column_func I
  C C1 P t Ab T KP window)) x y);

symbol homology_window_right_first_hom_expanded_path [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)]
  : τ (@= (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
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
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x y))
≔ @eq_refl (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
  walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y))) (@comp_cat_fapp0
  (Hom_cat I x y) (Hom_cat (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@homology_window_right_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@homology_window_right_column_func I C C1 P t Ab T KP window) y)) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P
  t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) y)) (@fapp1_func (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat
  C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
  (@homology_window_right_column_func I C C1 P t Ab T KP window) x y));

symbol homology_window_left_first_hom_whole_path [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)]
  : τ (@= (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) y))) (@fapp1_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C
    t T) C (@zero_arrow_cone_first_func C t T) (@homology_window_left_column_func I C C1 P t Ab T KP window)) x y)
    (@fapp1_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x y))
≔ @eq_refl (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C
  (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P
  t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window))) y))) (@fapp1_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t
  T) C (@zero_arrow_cone_first_func C t T) (@homology_window_left_column_func I C C1 P t Ab T KP window)) x y);

symbol homology_window_left_first_hom_expanded_path [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)]
  : τ (@= (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
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
    (@homology_window_left_column_func I C C1 P t Ab T KP window) x y)) (@fapp1_func I C (@comp_cat_fapp0 I
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T window))) x y))
≔ @eq_refl (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C
  (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P
  t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window))) y))) (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat
  (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP
  window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (Hom_cat
  C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t
  T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
  Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
  (@homology_window_left_column_func I C C1 P t Ab T KP window) x y));

symbol homology_window_right_diagram_hom_whole_path [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)]
  : τ (@= (Functor (Hom_cat I x y) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C)
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
    (@computational_abelian_preabelian C P t Ab) T window))) y))) (@fapp1_func I (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T)
    (@homology_window_right_column_func I C C1 P t Ab T KP window)) x y) (@fapp1_func I (Functor_cat WalkingArrow_cat C)
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
    (@computational_abelian_preabelian C P t Ab) T window))) x y))
≔ @eq_refl (Functor (Hom_cat I x y) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
  walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P
  t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
  T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)))
  (@homology_window_family_G I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat
  WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
  walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
  (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@homology_window_family_G I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)))
  (@fapp1_func I (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window))
  x y);

symbol homology_window_right_diagram_hom_expanded_path [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)]
  : τ (@= (Functor (Hom_cat I x y) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C)
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
    (@computational_abelian_preabelian C P t Ab) T window))) x y))
≔ @eq_refl (Functor (Hom_cat I x y) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
  walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P
  t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
  T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)))
  (@homology_window_family_G I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat
  WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
  walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
  (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@homology_window_family_G I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)))
  (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@homology_window_right_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@homology_window_right_column_func I C C1 P t Ab T KP window) y)) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I
  (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
  walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
  (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@homology_window_family_G I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x)
  (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
  walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
  (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@homology_window_family_G I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y))
  (@fapp1_func (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat
  C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
  (@homology_window_right_column_func I C C1 P t Ab T KP window) x y));

symbol homology_window_left_diagram_hom_whole_path [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)]
  : τ (@= (Functor (Hom_cat I x y) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C)
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
    (@computational_abelian_preabelian C P t Ab) T window))) y))) (@fapp1_func I (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T)
    (@homology_window_left_column_func I C C1 P t Ab T KP window)) x y) (@fapp1_func I (Functor_cat WalkingArrow_cat C)
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
    (@computational_abelian_preabelian C P t Ab) T window))) x y))
≔ @eq_refl (Functor (Hom_cat I x y) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
  (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func
  I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@homology_window_family_J I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x)
  (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C
  t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1
  I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@homology_window_family_J I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)))
  (@fapp1_func I (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@homology_window_left_column_func I C C1 P t Ab T KP window)) x
  y);

symbol homology_window_left_diagram_hom_expanded_path [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)]
  : τ (@= (Functor (Hom_cat I x y) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C)
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
    (@computational_abelian_preabelian C P t Ab) T window))) x y))
≔ @eq_refl (Functor (Hom_cat I x y) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
  (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func
  I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@homology_window_family_J I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x)
  (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C
  t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1
  I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@homology_window_family_J I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)))
  (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I
  (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C
  t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1
  I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@homology_window_family_J I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x)
  (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C
  t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1
  I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@homology_window_family_J I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y))
  (@fapp1_func (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat
  C t T) (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
  (@homology_window_left_column_func I C C1 P t Ab T KP window) x y));

/* Evaluation consequences of the whole Hom comparisons.
   Keep the full Hom functors as the operational owners: no additional
   globally capped projection-order equality is assumed. */
symbol homology_window_right_first_action_path [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] (u : τ
    (Hom I x y))
  : τ (@= (Hom C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
    walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp0 (Hom_cat I x y) (Hom_cat C (@fapp0 I C
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
    (@computational_abelian_preabelian C P t Ab) T window))) x y) u))
≔ @eq_ap (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
  walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y))) (Hom C (@fapp0 I C
  (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t
  T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) y))
    (λ F : τ (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T)
      C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) y))), @fapp0 (Hom_cat I x y) (Hom_cat C (@fapp0 I C
      (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
      (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm
      I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I
      (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C
      C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) y)) F u)
    (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
      (@homology_window_right_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
      (@homology_window_right_column_func I C C1 P t Ab T KP window) y)) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I
      (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C
      C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T)
      C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_rowm I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P
      t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP
      window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T) (@homology_window_right_column_func I C C1 P t Ab T KP window) x
      y)) (@fapp1_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
      walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
      (@homology_window_family_rowm I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x y)
    (@homology_window_right_first_hom_expanded_path I C C1 P t Ab T KP window x y);

symbol homology_window_right_diagram_action_path [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] (u : τ
    (Hom I x y))
  : τ (@= (Hom (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C
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
    (@computational_abelian_preabelian C P t Ab) T window))) x y) u))
≔ @eq_ap (Functor (Hom_cat I x y) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
  walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P
  t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
  T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)))
  (@homology_window_family_G I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat
  WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
  walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
  (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@homology_window_family_G I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)))
  (Hom (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C
  (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C
  t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
  walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P
  t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t
  T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
  (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)))
  (@homology_window_family_G I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y))
    (λ F : τ (Functor (Hom_cat I x y) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C)
      (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
      walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
      (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
      (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C
      C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C
      t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
      (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
      walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
      (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
      (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C
      C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C
      t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) y))), @fapp0 (Hom_cat I x y) (Hom_cat (Functor_cat
      WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I
      (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C
      C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C
      t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
      (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
      walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
      (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
      (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C
      C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C
      t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) y)) F u)
    (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
      (@homology_window_right_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
      (@homology_window_right_column_func I C C1 P t Ab T KP window) y)) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I
      (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C
      t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
      (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T
      walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
      (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
      (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C
      C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C
      t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
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
      (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C
      C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C
      t T) C (@zero_arrow_cone_vertex_func C t T walking_arrow_tgt) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_G I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) x y)
    (@homology_window_right_diagram_hom_expanded_path I C C1 P t Ab T KP window x y);

symbol homology_window_left_first_action_path [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] (u : τ
    (Hom I x y))
  : τ (@= (Hom C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I
    C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat
    C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian
    C P t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y))
    (@fapp0 (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
    Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C
    (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1
    P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
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
    (@computational_abelian_preabelian C P t Ab) T window))) x y) u))
≔ @eq_ap (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C
  (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P
  t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window))) y))) (Hom C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C
  t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P
  t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C
  (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P
  t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window))) y))
    (λ F : τ (Functor (Hom_cat I x y) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
      Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C
      (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C
      C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) y))), @fapp0 (Hom_cat I x y) (Hom_cat C (@fapp0 I C
      (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C
      C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T)
      C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P
      t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)) F u)
    (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
      (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
      (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (Hom_cat C (@fapp0 I C (@comp_cat_fapp0 I
      (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T)
      C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P
      t Ab) T (@homology_window_family_row0 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y))
      (@fapp1_func (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
      (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
      (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
      (@homology_window_left_column_func I C C1 P t Ab T KP window) x y)) (@fapp1_func I C (@comp_cat_fapp0 I
      (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row0 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) x y)
    (@homology_window_left_first_hom_expanded_path I C C1 P t Ab T KP window x y);

symbol homology_window_left_diagram_action_path [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t
    T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (window : τ (@HomologyWindowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) [x y : τ (Obj I)] (u : τ
    (Hom I x y))
  : τ (@= (Hom (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C
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
    (@computational_abelian_preabelian C P t Ab) T window))) x y) u))
≔ @eq_ap (Functor (Hom_cat I x y) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C
  C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
  (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func
  I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@homology_window_family_J I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x)
  (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C
  t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1
  I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@homology_window_family_J I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y)))
  (Hom (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C
  (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P
  t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
  (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func
  I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@homology_window_family_J I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) x)
  (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab)
  T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C
  t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1
  I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian
  C P t Ab) T window))) (@homology_window_family_J I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) y))
    (λ F : τ (Functor (Hom_cat I x y) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C)
      (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
      (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1
      I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
      Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
      (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
      (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1
      I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
      (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
      (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1
      I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
      Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
      (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
      (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1
      I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) y))), @fapp0 (Hom_cat I x y) (Hom_cat (Functor_cat
      WalkingArrow_cat C) (@fapp0 I (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I
      (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
      Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
      (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
      (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1
      I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
      (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
      (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1
      I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
      Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
      (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
      (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1
      I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) y)) F u)
    (@comp_cat_fapp0 (Hom_cat I x y) (Hom_cat (@ZeroArrowCone_cat C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
      (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
      (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 I
      (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
      Ab) T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)))
      (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C
      C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C
      t T) C (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian
      C P t Ab) T (@homology_window_family_row1 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))
      (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2
      I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) x) (@fapp0 I (Functor_cat WalkingArrow_cat C)
      (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
      (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1
      I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
      Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
      (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
      (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1
      I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) y)) (@fapp1_func (@ZeroArrowCone_cat C t T) (Functor_cat
      WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
      (@homology_window_left_column_func I C C1 P t Ab T KP window) x) (@fapp0 I (@ZeroArrowCone_cat C t T)
      (@homology_window_left_column_func I C C1 P t Ab T KP window) y)) (@fapp1_func I (@ZeroArrowCone_cat C t T)
      (@homology_window_left_column_func I C C1 P t Ab T KP window) x y)) (@fapp1_func I (Functor_cat WalkingArrow_cat C)
      (@transf_arrow_diagram_func I C (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
      (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1
      I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_first_func C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
      Ab) T (@homology_window_family_row2 I C C1 P t (@computational_abelian_preabelian C P t Ab) T window))) (@fapp0 _ _
      (@comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
      (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row1
      I C C1 P t (@computational_abelian_preabelian C P t Ab) T window)) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T (@homology_window_family_row2 I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) (@homology_window_family_J I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T window))) x y)
    (@homology_window_left_diagram_hom_expanded_path I C C1 P t Ab T KP window x y);
