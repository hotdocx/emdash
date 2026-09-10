/*
  The whole-H inclusion kills the direct connecting arrow.
  Its image on the connecting lift is a retained middle boundary. The
  existing quotient and epic factors then give the two descents. The
  public theorem uses actual whole H action with no extra square inputs.
*/
require open emdash.emdash3_2_homology_connecting_target_cycles;
require open emdash.emdash3_2_short_exact_row_chain_projection;
require open emdash.emdash3_2_homology_record_boundary_factors;
require open emdash.emdash3_2_homology_record_cancellation;
require open emdash.emdash3_2_hom_factor_zero_descent;
require open emdash.emdash3_2_homology_record_connecting;
require open emdash.emdash3_2_chain_pair_homology_actions;

symbol homology_connecting_inclusion_boundary_factor
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
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
    A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
    row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
    A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
    row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero) HT))))
  : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
    Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0
    B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
    row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) B0 B1 (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) (@homology_connecting_cover_middle C P t Ab A0 B0 Dm D0 D1 row0
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H)))
≔ @hom_postcomp_factor_intro C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
  (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
  Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
  rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C
  (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
  Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
  rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H) B0 B1 (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) (@homology_connecting_cover_middle C P t Ab A0 B0 Dm D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H)) (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G
  J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G
  J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G
  J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G
  J lower_zero) HT)) cf) (@homology_connecting_target_lift C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1 row2 G J
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
  Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero) lower_zero H HT))
    (@eq_trans _ _ _ _
      (@hom_postcomp_factor_path C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
        (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
        B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
        row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_connecting_left_lift C P t Ab A0 B0 D0 A1 B1 D1 Dm
        row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) H))
        (@hom_postcomp_factor_paste C (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0
        B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
        row1 row2 G J lower_zero) HB) B1
      (@id C (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
        A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
        row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
        (@homology_connecting_left_lift C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) H) (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
      (@homology_connecting_target_factor C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1 row2 G J
        (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
        rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) lower_zero H HT) cf))
      (@homology_connecting_left_reconstruction C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) H));

symbol homology_connecting_inclusion_covered_zero
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
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
    A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
    row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
    A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
    row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero) HT)))) (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2
    D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
    A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
    row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
    B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0
    B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
    row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
    row1 row2 G J lower_zero) HT)) cf))))
  : τ (@= (Hom C (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0
    B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero) HB))
      (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab
        A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
        (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
        row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
        (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
        (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
        row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
        (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
        row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0
        B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
        row1 row2 G J lower_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
        (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0
        B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
        row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
        row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
        row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
        (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
        row0 row1 row2 G J lower_zero) HT)) cf)) hf) (@homology_connecting_covered_homology_map C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2
        Dm row0 row1 row2 G J (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) lower_zero H HT))
      (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
        B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
        row2 G J lower_zero) HB)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@hom_factor_paste_path C (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
        (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
        row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
        row2 G J lower_zero) HB)
        (@id C (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0
          D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H))
          (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
          A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
          row0 row1 row2 G J lower_zero) HT) (@id C (@homology_record_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB))
          (@homology_connecting_target_lift C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1 row2 G J
          (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
          rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero) lower_zero H HT) (@comp_fapp0 C (@homology_record_cycle_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
          (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
          row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
          (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1
          B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
          row1 row2 G J lower_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
          (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
          (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
          A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
          row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C
          (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
          A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
          row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
          (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
          row1 row2 G J lower_zero) HT)) cf)) (@homology_connecting_covered_homology_map C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0
          row1 row2 G J (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) lower_zero H HT)
          (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
          (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
          A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
          row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
          (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
          A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
          row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C
          P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
          (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
          B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
          row0 row1 row2 G J lower_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
          (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0
          B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
          row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
          (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
          row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
          (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
          B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
          (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
          row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
          (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
          row1 row2 G J lower_zero) HT)) cf)) hf)
        (@eq_refl (Hom C (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t
          Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
          (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
          A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
          row1 row2 G J lower_zero) HT)) (@homology_connecting_covered_homology_map C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1
          row2 G J (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) lower_zero H HT))
        (@eq_sym _ _ _ (@hom_precomp_factor_path C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
          (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
          A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
          row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
          (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
          A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
          row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C
          P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
          (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
          B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
          row0 row1 row2 G J lower_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
          (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0
          B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
          row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
          (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
          row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
          (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
          B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
          (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
          row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
          (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
          row1 row2 G J lower_zero) HT)) cf)) hf))))
    (@eq_trans _ _ _ _
      (@eq_sym _ _ _ (@comp_assoc C (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0
        B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
        row1 row2 G J lower_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
        (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0
        B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
        row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
        row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
        row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
        (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
        row0 row1 row2 G J lower_zero) HT)) cf) (@homology_connecting_target_lift C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1
        row2 G J (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
        C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm
        Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) lower_zero H HT)))
      (@homology_record_boundary_factor_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2
        D2 row0 row1 row2 G J lower_zero) HB (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) (@homology_connecting_cover_middle C P t Ab A0 B0 Dm D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) (@homology_connecting_inclusion_boundary_factor C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2
        rowm row0 row1 row2 F G J upper_zero lower_zero H HT HB cf)));

symbol homology_connecting_inclusion_cycles_zero
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
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
    A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
    row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
    A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
    row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero) HT)))) (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2
    D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
    A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
    row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
    B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0
    B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
    row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
    row1 row2 G J lower_zero) HT)) cf))))
  : τ (@= (Hom C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB))
      (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
        C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
        (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
        rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
        row2 G J lower_zero) HB) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive
        C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
        (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
        row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
        (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
        row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0
        B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
        row1 row2 G J lower_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
        (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0
        B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
        row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
        row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
        row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
        (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
        row0 row1 row2 G J lower_zero) HT)) cf)) hf) (@homology_connecting_cycles_map C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0
        row1 row2 G J (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) lower_zero H HT))
      (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
        D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)))
≔ @epic_factor_postzero_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
  Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
  rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
  row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2
  D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_connecting_cover_projection C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
      B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
      (@homology_connecting_covered_homology_map C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1 row2 G J
      (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) lower_zero H HT) (@hom_precomp_factor_intro C (@homology_connecting_cover_object C P t Ab A0 B0 Dm
      D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
      C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
      (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
      row2 G J lower_zero) HT) (@homology_connecting_cover_projection C P t Ab A0 B0 Dm D0 D1 row0
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) H) (@homology_connecting_covered_homology_map C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1 row2
      G J (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
      Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) lower_zero H HT) (@homology_connecting_cycles_map C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1
      row2 G J (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
      P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
      rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) lower_zero H HT)
      (@homology_connecting_cycles_reconstruction C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1 row2 G J
        (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
        rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) lower_zero H HT))
    (@homology_connecting_cover_epic C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
      Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
      (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
      (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
      row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
      A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
      row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0
      B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
      row1 row2 G J lower_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1
      B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
      row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C
      P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
      A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
      row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
      A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
      row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
      (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
      row2 G J lower_zero) HT)) cf)) hf)
    (@homology_connecting_inclusion_covered_zero C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
      lower_zero H HT HB cf hf);

symbol homology_record_connecting_inclusion_zero
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
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
    A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
    row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
    A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
    row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero) HT)))) (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2
    D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
    A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
    row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
    B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0
    B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
    row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
    row1 row2 G J lower_zero) HT)) cf))))
  : τ (@= (Hom C (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB))
      (@comp_fapp0 C (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
        (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
        rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
        row2 G J lower_zero) HB) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive
        C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
        (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
        row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
        (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
        row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0
        B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
        row1 row2 G J lower_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
        (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0
        B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
        row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
        row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
        row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
        (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
        row0 row1 row2 G J lower_zero) HT)) cf)) hf) (@homology_record_connecting C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm
        row0 row1 row2 F G J upper_zero lower_zero H HT))
      (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)))
≔ @epic_factor_postzero_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am
  Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2
  D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) H) (@homology_connecting_cycles_map C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1 row2 G J
      (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) lower_zero H HT) (@homology_record_connecting_factor C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2
      rowm row0 row1 row2 F G J upper_zero lower_zero H HT)
    (@homology_record_projection_epic C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
      D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) H)
    (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
      (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
      row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
      A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
      row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0
      B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
      row1 row2 G J lower_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1
      B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
      row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C
      P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
      A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
      row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
      A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
      row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
      (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
      row2 G J lower_zero) HT)) cf)) hf) (@homology_connecting_inclusion_cycles_zero C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2
      rowm row0 row1 row2 F G J upper_zero lower_zero H HT HB cf hf);

symbol homology_whole_connecting_inclusion_zero
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
  : τ (@= (Hom C (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))
    (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)))) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP)
    (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
    (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))))
      (@comp_fapp0 C (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P
        t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
        (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
        Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))) (@fapp0
        (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t
        Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
        (@computational_abelian_preabelian C P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@fapp0
        (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t
        Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
        (@computational_abelian_preabelian C P t Ab)) KP B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)))
        (@chain_pair_homology_action C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t
        T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
        (@computational_abelian_preabelian C P t Ab)) KP QP A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
        row2 G J lower_zero) (@short_exact_row_chain_inclusion C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
        A2 B2 D2 row0 row1 row2 G J lower_zero))
        (@homology_record_connecting C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero
          (@chain_pair_homology_record C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1
          t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
          (@computational_abelian_preabelian C P t Ab)) KP QP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
          D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))
          (@chain_pair_homology_record C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1
          t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
          (@computational_abelian_preabelian C P t Ab)) KP QP A0 A1 A2 (@short_exact_row_chain_source_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))))
      (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@fapp0
        (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t
        Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
        (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
        Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))) (@fapp0
        (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t
        Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
        (@computational_abelian_preabelian C P t Ab)) KP B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)))))
≔ @homology_record_connecting_inclusion_zero C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
  lower_zero (@chain_pair_homology_record C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
  row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero))) (@chain_pair_homology_record C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))
  (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP A0 A1 A2 (@short_exact_row_chain_source_pair C P
  t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))
  (@chain_pair_homology_record C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
  (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))
  (@chain_pair_homology_cycle_action_factor C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G
  J lower_zero) (@short_exact_row_chain_inclusion C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
  row1 row2 G J lower_zero)) (@chain_pair_homology_action_factor C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))
  (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G
  J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_inclusion C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero));
