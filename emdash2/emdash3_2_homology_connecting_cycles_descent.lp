/* The covered map kills the actual cover kernel, hence descends to source cycles. */
require open emdash.emdash3_2_homology_connecting_target_cycles;
require open emdash.emdash3_2_homology_connecting_cover_kernel_boundary;
require open emdash.emdash3_2_homology_record_boundary_factors;

symbol homology_connecting_cover_kernel_target_boundary
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 X : τ (Obj C)]
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2)))
  (incoming : τ (Hom C X D0))
  (source_zero : τ (@= (Hom C X D1) (@comp_fapp0 C X D0 D1 (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) incoming)
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D1)))
  (middle_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G))
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero)))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J middle_zero)))
  : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J middle_zero) HT) A1
    (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
    B1 D1 X row0 row1 G incoming source_zero) H) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J middle_zero) HT) (@comp_fapp0 C
    (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
    B1 D1 X row0 row1 G incoming source_zero) H) A0 A1 (@computational_chain_pair_map_next C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) (@homology_connecting_cover_kernel_left C P t Ab A0 B0 D0 A1 B1
    D1 X row0 row1 G incoming source_zero H)))
≔ @hom_postcomp_factor_intro C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J middle_zero) HT) A1
  (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
  B1 D1 X row0 row1 G incoming source_zero) H) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J middle_zero) HT) (@comp_fapp0 C
  (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
  B1 D1 X row0 row1 G incoming source_zero) H) A0 A1 (@computational_chain_pair_map_next C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) (@homology_connecting_cover_kernel_left C P t Ab A0 B0 D0 A1 B1 D1
  X row0 row1 G incoming source_zero H))
    (@comp_fapp0 C (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t
      Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H) (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H)
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
      A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
      row1 row2 G J middle_zero) HT) (@homology_connecting_target_lift C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 X row0 row1 row2 G J
      incoming source_zero middle_zero H HT) (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H))
    (@eq_trans _ _ _ _
      (@hom_factor_paste_path C (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H)
        (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
        D1 X row0 row1 G incoming source_zero) H) (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H) A1
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
        row1 row2 G J middle_zero) HT) A1
        (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0
          B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H) (@homology_connecting_left_lift C P t Ab A0 B0 D0 A1 B1 D1 X row0
          row1 G incoming source_zero H) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J middle_zero) HT)
          (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0
          B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H) (@homology_connecting_target_lift C P t Ab A0 B0 D0 A1 B1 D1 A2 B2
          D2 X row0 row1 row2 G J incoming source_zero middle_zero H HT) (@homology_connecting_left_lift C P t Ab A0 B0 D0 A1 B1 D1
          X row0 row1 G incoming source_zero H) (@id C A1)
        (@eq_refl (Hom C (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair
          C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H) A1) (@comp_fapp0 C
          (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0
          D0 A1 B1 D1 X row0 row1 G incoming source_zero) H) (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
          (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H) A1
          (@homology_connecting_left_lift C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero H)
          (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0
          B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H)))
        (@homology_connecting_target_reconstruction C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 X row0 row1 row2 G J incoming source_zero
          middle_zero H HT))
      (@homology_connecting_left_on_cover_kernel_path C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero H));

symbol homology_connecting_covered_map_kernel_zero
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 X : τ (Obj C)]
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2)))
  (incoming : τ (Hom C X D0))
  (source_zero : τ (@= (Hom C X D1) (@comp_fapp0 C X D0 D1 (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) incoming)
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D1)))
  (middle_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G))
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero)))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J middle_zero)))
  : τ (@= (Hom C (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t
    Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H) (@homology_record_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J middle_zero) HT)) (@comp_fapp0 C
    (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
    B1 D1 X row0 row1 G incoming source_zero) H) (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J middle_zero) HT) (@homology_connecting_covered_homology_map C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 X row0 row1 row2 G J
    incoming source_zero middle_zero H HT) (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H))
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
      A1 B1 D1 X row0 row1 G incoming source_zero) H) (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J middle_zero) HT)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _ (@comp_assoc C (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H)
      (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
      D1 X row0 row1 G incoming source_zero) H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J middle_zero) HT)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
      (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
      row2 G J middle_zero) HT) (@homology_record_projection C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J middle_zero) HT)
      (@homology_connecting_target_lift C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 X row0 row1 row2 G J incoming source_zero middle_zero H
      HT) (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0
      B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H)))
    (@homology_record_boundary_factor_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
      Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2
      D2 row0 row1 row2 G J middle_zero) HT (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H)
      (@homology_connecting_cover_kernel_left C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero H)
      (@homology_connecting_cover_kernel_target_boundary C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 X row0 row1 row2 G J incoming
      source_zero middle_zero H HT));

symbol homology_connecting_cover_normal_test
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 X : τ (Obj C)]
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2)))
  (incoming : τ (Hom C X D0))
  (source_zero : τ (@= (Hom C X D1) (@comp_fapp0 C X D0 D1 (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) incoming)
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D1)))
  (middle_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G))
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero)))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J middle_zero)))
  : τ (@NormalEpiTest C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
    X row0 row1 G incoming source_zero) H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) X D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0
    row1 G incoming source_zero) H) (@homology_connecting_cover_projection C P t Ab A0 B0 X D0 D1 row0
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H)
    (@homology_connecting_cover_kernel C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
    X row0 row1 G incoming source_zero) H) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J middle_zero) HT))
≔ @Struct_sigma (Hom C (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab
  A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J middle_zero) HT))
    (λ h : τ (Hom C (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0
      B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H) (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J middle_zero) HT)), @= (Hom C
      (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
      A1 B1 D1 X row0 row1 G incoming source_zero) H) (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J middle_zero) HT))
      (@comp_fapp0 C (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P
        t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H) (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
        (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
        row2 G J middle_zero) HT) h (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H))
        (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0
        D0 A1 B1 D1 X row0 row1 G incoming source_zero) H) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J middle_zero) HT)))
    (@homology_connecting_covered_homology_map C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 X row0 row1 row2 G J incoming source_zero
      middle_zero H HT) (@homology_connecting_covered_map_kernel_zero C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 X row0 row1 row2 G J
      incoming source_zero middle_zero H HT);

symbol homology_connecting_cycles_map
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 X : τ (Obj C)]
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2)))
  (incoming : τ (Hom C X D0))
  (source_zero : τ (@= (Hom C X D1) (@comp_fapp0 C X D0 D1 (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) incoming)
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D1)))
  (middle_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G))
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero)))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J middle_zero)))
  : τ (Hom C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) X D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J middle_zero) HT))
≔ @colift_along_epimorphism C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@computational_abelian_epi_colifts C P t Ab)
    (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
      X row0 row1 G incoming source_zero) H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) X D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0
      row1 G incoming source_zero) H) (@homology_connecting_cover_projection C P t Ab A0 B0 X D0 D1 row0
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H)
      (@homology_connecting_cover_epic C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
      X row0 row1 G incoming source_zero) H) (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J middle_zero) HT)
      (@homology_connecting_cover_normal_test C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 X row0 row1 row2 G J incoming source_zero
      middle_zero H HT);

symbol homology_connecting_cycles_reconstruction
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 X : τ (Obj C)]
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2)))
  (incoming : τ (Hom C X D0))
  (source_zero : τ (@= (Hom C X D1) (@comp_fapp0 C X D0 D1 (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) incoming)
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D1)))
  (middle_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G))
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero)))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J middle_zero)))
  : τ (@= (Hom C (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0
    D0 A1 B1 D1 X row0 row1 G incoming source_zero) H) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J middle_zero) HT)) (@comp_fapp0 C
    (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
    X row0 row1 G incoming source_zero) H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) X D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0
    row1 G incoming source_zero) H) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J middle_zero) HT)
    (@homology_connecting_cycles_map C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 X row0 row1 row2 G J incoming source_zero middle_zero H HT)
      (@homology_connecting_cover_projection C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
      B1 D1 X row0 row1 G incoming source_zero) H)) (@homology_connecting_covered_homology_map C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 X
      row0 row1 row2 G J incoming source_zero middle_zero H HT))
≔ @colift_along_epimorphism_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@computational_abelian_epi_colifts C P t Ab)
    (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
      X row0 row1 G incoming source_zero) H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) X D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0
      row1 G incoming source_zero) H) (@homology_connecting_cover_projection C P t Ab A0 B0 X D0 D1 row0
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming source_zero) H)
      (@homology_connecting_cover_epic C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
      X row0 row1 G incoming source_zero) H) (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J middle_zero) HT)
      (@homology_connecting_cover_normal_test C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 X row0 row1 row2 G J incoming source_zero
      middle_zero H HT);
