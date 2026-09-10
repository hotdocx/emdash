/*
  First interior exactness of the existing whole-H window.
  An annihilated test is covered, corrected by an actual boundary and
  factored through the original row kernel and left cycles. The existing
  local-cover criterion proves exactness at H(B). The public whole-H
  theorem derives all factors and boundary naturality from the original
  rows and coherent model data. The other two interiors remain downstream.
*/
require open emdash.emdash3_2_homology_map_corrections;
require open emdash.emdash3_2_homology_window;
require open emdash.emdash3_2_homology_record_cycle_lifts;
require open emdash.emdash3_2_homology_boundary_naturality;

symbol homology_record_first_window_pair [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
    Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F))
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (HA : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (HC : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero))))
  (cfi : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0
    A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HA) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0
    A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HA) A0 B0 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HA)))) (cfp : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB))))
  (hfi : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HA) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0
    A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HA) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
    B1 D1 rowm row0 row1 F G upper_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) B0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA) A0 B0
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
    A0 A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HA)) cfi)))) (hfp : τ (@HomPrecompFactor C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0
    B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB)) cfp))))
  : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HA) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC))
≔ @computational_chain_pair_intro C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) HA) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
  rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
  row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) HC) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA)
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) HA) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
  rowm row0 row1 F G upper_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA) (@comp_fapp0 C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) HA) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
  (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) HA) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) HA) A0 B0 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) HA)) cfi)) hfi) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
  Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) HC) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
  Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
  row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) HC) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
  row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0
  D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
  (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0
  B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero) HB)) cfp)) hfp)
    (@homology_record_map_factors_composite_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
      t Ab))
      Am A0 A1 Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0
        B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C
        P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
        B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))
      HA HB HC (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
        t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) cfi cfp hfi
        hfp
      (@computational_chain_pair_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)));

symbol homology_first_row_test [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
    Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F))
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (HA : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (HC : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero))))
  (cfi : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0
    A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HA) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0
    A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HA) A0 B0 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HA)))) (cfp : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB))))
  (hfi : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HA) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0
    A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HA) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
    B1 D1 rowm row0 row1 F G upper_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) B0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA) A0 B0
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
    A0 A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HA)) cfi)))) (hfp : τ (@HomPrecompFactor C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0
    B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB)) cfp))))
  (boundary_path : τ (@= (Hom C Bm (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC))
    (@comp_fapp0 C Bm (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
      C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
      A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC)
      (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC) D0
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
      B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) HB) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0 C
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
      B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) HB) B0 D0 (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
      row1 F G upper_zero) HB)) cfp) (@homology_record_boundary C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB))
    (@comp_fapp0 C Bm Dm (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC)
      (@homology_record_boundary C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)))))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0
    B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB)) cfp)) hfp) T))
  : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))))
≔ @Struct_sigma (Hom C (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
  row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0
  D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
  (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0
  B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) B0)
    (λ h : τ (Hom C (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
      (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
      rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) B0), @= (Hom C (@homology_map_correction_object C P t Ab Bm B0
      B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
      rowm row0 row1 F G upper_zero) (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
      (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
      (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
      rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) D0)
      (@comp_fapp0 C (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
        C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
        rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) B0 D0 (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) h)
        (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
        C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
        rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) D0))
    (@comp_fapp0 C (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
      (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
      rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
      row1 F G upper_zero) HB) B0 (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_map_corrected_cycle C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
      (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
      rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))))
    (@eq_trans _ _ _ _
      (@eq_sym _ _ _
        (@hom_factor_paste_path C (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C
          P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
          (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
          (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
          (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
          (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
          rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C
          P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
          (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
          B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
          (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
          B1 D1 rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)))
          (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
          (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
          (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
          (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
          (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
          rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C
          P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
          (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
          B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
          (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
          B1 D1 rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)))
          (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
          Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero) HB) B0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
          row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC) D0
          (@id C (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
            (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
            (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
            (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
            (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
            t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm
            Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive
            C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
            (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
            A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
            (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))))
            (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P
            t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
            D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC)
            (@homology_map_corrected_cycle C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
            (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
            (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
            (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
            (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
            t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm
            Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive
            C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
            (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
            A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
            (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)))
            (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
            Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC) D0
            (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P
            t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
            D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0
            C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0 (@computational_chain_pair_d C (@computational_homology_preadditive C
            P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
            (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
            row0 row1 F G upper_zero) HB)) cfp) (@comp_fapp0 C (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1
            (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
            row0 row1 F G upper_zero) (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
            (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
            t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm
            Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
            (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
            (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
            (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
            t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm
            Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive
            C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
            (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
            A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
            (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)))
            (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 (@homology_record_cycle_embedding C (@computational_homology_preadditive
            C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
            (@homology_map_corrected_cycle C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
            (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
            (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
            (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
            (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
            t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm
            Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive
            C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
            (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
            A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
            (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))))
            (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
            A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
          (@eq_refl (Hom C (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
            (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
            (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
            (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
            (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
            t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm
            Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive
            C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
            (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
            A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
            (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) B0)
            (@comp_fapp0 C (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
            (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
            (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
            (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
            (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
            t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm
            Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive
            C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
            (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
            A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
            (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)))
            (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 (@homology_record_cycle_embedding C (@computational_homology_preadditive
            C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
            (@homology_map_corrected_cycle C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
            (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
            (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
            (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
            (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
            t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm
            Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive
            C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
            (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
            A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
            (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)))))
          (@hom_postcomp_factor_path C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
            Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC) D0
            (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P
            t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
            D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0
            C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0 (@computational_chain_pair_d C (@computational_homology_preadditive C
            P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
            (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
            row0 row1 F G upper_zero) HB)) cfp)))
      (@preadditive_postcompose_zero_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
        C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
        rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
        row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC)
        (@comp_fapp0 C (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
          (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
          (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
          (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
          (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
          rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C
          P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
          (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
          B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
          (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
          B1 D1 rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)))
          (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
          Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
          row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC)
          (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
          row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC) D0
          (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
          Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero) HB) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
          row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0 C
          (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
          Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero) HB) B0 D0 (@computational_chain_pair_d C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
          (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
          row0 row1 F G upper_zero) HB)) cfp) (@homology_map_corrected_cycle C P t Ab Bm B0 B1 Dm D0 D1
          (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
          row0 row1 F G upper_zero) (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
          (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
          rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
          (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
          (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
          (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
          rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C
          P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
          (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
          B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
          (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
          B1 D1 rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))))
        (@homology_map_corrected_cycle_zero C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
          (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
          (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
          (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
          (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
          rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C
          P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
          (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
          B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
          (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
          B1 D1 rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)) boundary_path)));

symbol homology_first_row_factor [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
    Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F))
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (HA : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (HC : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero))))
  (cfi : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0
    A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HA) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0
    A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HA) A0 B0 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HA)))) (cfp : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB))))
  (hfi : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HA) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0
    A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HA) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
    B1 D1 rowm row0 row1 F G upper_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) B0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA) A0 B0
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
    A0 A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HA)) cfi)))) (hfp : τ (@HomPrecompFactor C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0
    B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB)) cfp))))
  (boundary_path : τ (@= (Hom C Bm (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC))
    (@comp_fapp0 C Bm (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
      C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
      A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC)
      (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC) D0
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
      B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) HB) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0 C
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
      B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) HB) B0 D0 (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
      row1 F G upper_zero) HB)) cfp) (@homology_record_boundary C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB))
    (@comp_fapp0 C Bm Dm (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC)
      (@homology_record_boundary C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)))))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0
    B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB)) cfp)) hfp) T))
  : τ (@HomPostcompFactor C A0 B0 (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C
    P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) (@computational_chain_pair_dnext C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@comp_fapp0 C
    (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) B0 (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_map_corrected_cycle C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)))))
≔ is_contr_center (@computational_kernel_factor_contr C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 D0 (@computational_chain_pair_d C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@short_exact_kernel_record C P t Ab A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P
      t Ab) A0 B0 D0 row0)
      (@computational_short_exact_row_evidence C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
        C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
        rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) (@homology_first_row_test C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1
        rowm row0 row1 F G upper_zero HA HB HC cfi cfp hfi hfp boundary_path T test));

symbol homology_first_cover [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
    Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F))
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (HA : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (HC : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero))))
  (cfi : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0
    A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HA) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0
    A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HA) A0 B0 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HA)))) (cfp : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB))))
  (hfi : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HA) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0
    A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HA) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
    B1 D1 rowm row0 row1 F G upper_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) B0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA) A0 B0
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
    A0 A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HA)) cfi)))) (hfp : τ (@HomPrecompFactor C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0
    B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB)) cfp))))
  (boundary_path : τ (@= (Hom C Bm (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC))
    (@comp_fapp0 C Bm (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
      C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
      A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC)
      (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC) D0
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
      B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) HB) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0 C
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
      B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) HB) B0 D0 (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
      row1 F G upper_zero) HB)) cfp) (@homology_record_boundary C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB))
    (@comp_fapp0 C Bm Dm (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC)
      (@homology_record_boundary C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)))))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0
    B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB)) cfp)) hfp) T))
  : τ (@ComputationalExactCoverWitness C P t (@computational_abelian_preabelian C P t Ab) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HA) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_first_window_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero
    HA HB HC cfi cfp hfi hfp) T test)
≔ @computational_exact_cover_intro C P t (@computational_abelian_preabelian C P t Ab) (@homology_record_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) HA) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
  rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
  row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) HC) (@homology_record_first_window_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero HA
  HB HC cfi cfp hfi hfp) T test
    (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
      (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
      rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) (@comp_fapp0 C (@homology_map_correction_object C P t Ab Bm B0
      B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
      rowm row0 row1 F G upper_zero) (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
      (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
      (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
      rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) (@homology_map_kernel_cover_object C P t Ab Bm B0 B1 Dm D0 D1
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
      row1 F G upper_zero) (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
      (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
      (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
      rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test) T (@homology_map_kernel_cover_epi C P t Ab Bm B0 B1 Dm D0 D1
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
      row1 F G upper_zero) (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
      (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
      (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
      rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test) (@homology_map_correction_step C P t Ab Bm B0 B1 Dm D0 D1
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
      row1 F G upper_zero) (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
      (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
      (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
      rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)))) (@homology_map_correction_is_epic C P t Ab Bm B0 B1 Dm D0 D1
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
      row1 F G upper_zero) (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
      (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
      (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
      rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)) (@computational_short_exact_epic C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_evidence C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)))
        (@hom_postcomp_factor_arrow C (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) HB) (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P
        t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
        C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
        rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
        (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) HA) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA) (@comp_fapp0 C
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
        A0 A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) HA) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
        A0 A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) HA) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
        A0 A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) HA) A0 B0 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
        (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) HA)) cfi)) hfi) (@comp_fapp0 C (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
        (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
        rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
        C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
        rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
        B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) HB) (@homology_map_corrected_cycle C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair
        C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
        C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
        rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)))) (@homology_record_cycle_lift_homology_factor C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Am A0 A1 Bm B0 B1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
        B1 D1 rowm row0 row1 F G upper_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab)
        Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA HB (@short_exact_row_chain_inclusion C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
        (@computational_short_exact_monic C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
      (@computational_short_exact_row_evidence C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
        (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
        C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
        rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) (@homology_map_corrected_cycle C P t Ab Bm B0 B1 Dm D0 D1
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
        (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
        rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
        C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
        rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) (@homology_first_row_factor C P t Ab Am Bm Dm A0 B0 D0 A1 B1
        D1 rowm row0 row1 F G upper_zero HA HB HC cfi cfp hfi hfp boundary_path T test) cfi hfi))
    (@eq_trans _ _ _ _
      (@hom_postcomp_factor_path C (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) HB) (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P
        t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
        C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
        rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
        (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) HA) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA) (@comp_fapp0 C
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
        A0 A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) HA) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
        A0 A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) HA) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
        A0 A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) HA) A0 B0 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
        (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) HA)) cfi)) hfi) (@comp_fapp0 C (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
        (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
        rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
        C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
        rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
        B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) HB) (@homology_map_corrected_cycle C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair
        C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
        C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
        rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)))) (@homology_record_cycle_lift_homology_factor C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Am A0 A1 Bm B0 B1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
        B1 D1 rowm row0 row1 F G upper_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab)
        Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA HB (@short_exact_row_chain_inclusion C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
        (@computational_short_exact_monic C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
      (@computational_short_exact_row_evidence C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
        (@homology_map_correction_object C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
        C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
        rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) (@homology_map_corrected_cycle C P t Ab Bm B0 B1 Dm D0 D1
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
        (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
        rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
        C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
        rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))) (@homology_first_row_factor C P t Ab Am Bm Dm A0 B0 D0 A1 B1
        D1 rowm row0 row1 F G upper_zero HA HB HC cfi cfp hfi hfp boundary_path T test) cfi hfi))
      (@homology_map_corrected_cycle_source_path C P t Ab Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HB HC (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
        C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
        rowm row0 row1 F G upper_zero) HB)) cfp) hfp T test (@computational_chain_pair_d C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm))));

symbol homology_first_covers
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
    Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F))
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (HA : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (HC : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero))))
  (cfi : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0
    A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HA) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0
    A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HA) A0 B0 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HA)))) (cfp : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB))))
  (hfi : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HA) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0
    A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HA) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
    B1 D1 rowm row0 row1 F G upper_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) B0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA) A0 B0
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
    A0 A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HA)) cfi)))) (hfp : τ (@HomPrecompFactor C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0
    B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB)) cfp)))) (boundary_path : τ (@= (Hom C Bm (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC))
    (@comp_fapp0 C Bm (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
      C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
      A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC)
      (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC) D0
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
      B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) HB) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0 C
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
      B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) HB) B0 D0 (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
      row1 F G upper_zero) HB)) cfp) (@homology_record_boundary C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB))
    (@comp_fapp0 C Bm Dm (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC)
      (@homology_record_boundary C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)))))
  : τ (@HasComputationalExactCovers C P t (@computational_abelian_preabelian C P t Ab) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HA) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_first_window_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero
    HA HB HC cfi cfp hfi hfp))
≔ λ T : τ (Obj C),
    λ test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
      row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC)
      (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
      row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0
      B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
      row1 F G upper_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
      D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0
      D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
      (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
      rowm row0 row1 F G upper_zero) HB)) cfp)) hfp) T),
      @homology_first_cover C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero HA HB HC cfi cfp hfi hfp boundary_path
        T test;

symbol homology_record_first_exact
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
    Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F))
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (HA : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (HC : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero))))
  (cfi : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0
    A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HA) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0
    A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HA) A0 B0 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HA)))) (cfp : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB))))
  (hfi : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HA) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0
    A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HA) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
    B1 D1 rowm row0 row1 F G upper_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) B0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HA) A0 B0
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
    A0 A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HA)) cfi)))) (hfp : τ (@HomPrecompFactor C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0
    B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB)) cfp)))) (boundary_path : τ (@= (Hom C Bm (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC))
    (@comp_fapp0 C Bm (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
      C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
      A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC)
      (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC) D0
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
      B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) HB) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC) (@comp_fapp0 C
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
      B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) HB) B0 D0 (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
      row1 F G upper_zero) HB)) cfp) (@homology_record_boundary C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB))
    (@comp_fapp0 C Bm Dm (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) HC)
      (@homology_record_boundary C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) HC) (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)))))
  (Hwin : τ (@ComputationalHomologyAt C P t (@computational_abelian_preabelian C P t Ab) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HA) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_first_window_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero
    HA HB HC cfi cfp hfi hfp)))
  : τ (@ComputationalExactAt C P t (@computational_abelian_preabelian C P t Ab) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HA) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) HC) (@homology_record_first_window_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero
    HA HB HC cfi cfp hfi hfp) Hwin)
≔ @computational_exact_at_from_covers C P t (@computational_abelian_preabelian C P t Ab) (@homology_record_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am A0 A1
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) HA) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
  rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
  row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) HC) (@homology_record_first_window_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero HA
  HB HC cfi cfp hfi hfp) Hwin
    (@homology_first_covers C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero HA HB HC cfi cfp hfi hfp
      boundary_path);

symbol homology_whole_window_first_covers
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
    Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F))
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G))
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
    (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T0
    (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  : τ (@HasComputationalExactCovers C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t
    T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
    (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP Am
    A0 A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP)
    (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
    (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))
    (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)))) (@homology_whole_window_first_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G
    J upper_zero lower_zero C1 T T0 KP QP))
≔ @homology_first_covers C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero (@chain_pair_homology_record C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP Am
  A0 A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) (@chain_pair_homology_record C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))
  (@chain_pair_homology_record C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
  (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
  row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero))) (@chain_pair_homology_cycle_action_factor C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))
  (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP Am A0 A1 Bm B0 B1
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
  rowm row0 row1 F G upper_zero) (@short_exact_row_chain_inclusion C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) (@chain_pair_homology_cycle_action_factor C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))
  (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP Bm B0 B1 Dm D0 D1
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) (@short_exact_row_chain_projection C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
  B1 D1 rowm row0 row1 F G upper_zero)) (@chain_pair_homology_action_factor C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))
  (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP Am A0 A1 Bm B0 B1
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
  rowm row0 row1 F G upper_zero) (@short_exact_row_chain_inclusion C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) (@chain_pair_homology_action_factor C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))
  (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP Bm B0 B1 Dm D0 D1
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) (@short_exact_row_chain_projection C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
  B1 D1 rowm row0 row1 F G upper_zero)) (@chain_pair_homology_boundary_action_path C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))
  (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP Bm B0 B1 Dm D0 D1
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) (@short_exact_row_chain_projection C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
  B1 D1 rowm row0 row1 F G upper_zero));

symbol homology_whole_window_first_exact
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
    Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F))
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G))
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
    (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T0
    (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  : τ (@ComputationalExactAt C P t (@computational_abelian_preabelian C P t Ab)
      (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t
        Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
        (@computational_abelian_preabelian C P t Ab)) KP Am A0 A1 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0
        (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t
        Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
        (@computational_abelian_preabelian C P t Ab)) KP Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0
        (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t
        Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
        (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
        Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
        (@homology_whole_window_first_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
        lower_zero C1 T T0 KP QP) (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) (@fapp0
        (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t
        Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
        (@computational_abelian_preabelian C P t Ab)) KP Am A0 A1 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0
        (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t
        Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
        (@computational_abelian_preabelian C P t Ab)) KP Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0
        (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t
        Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
        (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
        Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
        (@homology_whole_window_first_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
        lower_zero C1 T T0 KP QP)))
≔ @computational_exact_at_from_covers C P t (@computational_abelian_preabelian C P t Ab)
    (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t
      Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
      (@computational_abelian_preabelian C P t Ab)) KP Am A0 A1 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0
      (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t
      Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
      (@computational_abelian_preabelian C P t Ab)) KP Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0
      (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t
      Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
      (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
      (@homology_whole_window_first_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
      lower_zero C1 T T0 KP QP) (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) (@fapp0
      (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t
      Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
      (@computational_abelian_preabelian C P t Ab)) KP Am A0 A1 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0
      (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t
      Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
      (@computational_abelian_preabelian C P t Ab)) KP Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0
      (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t
      Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
      (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
      (@homology_whole_window_first_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
      lower_zero C1 T T0 KP QP)) (@homology_whole_window_first_covers C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1
      row2 F G J upper_zero lower_zero C1 T T0 KP QP);
