/*
  The whole-H projection is killed by the direct connecting arrow.
  Generic reference helpers retain existing Hom factors; the public whole-H
  theorem derives those factors from naturality of the actual structural
  transformations. The preceding middle cycles lift into the same cover.
  No splitting, new normal test assumption or endpoint transport is used.
*/
require open emdash.emdash3_2_homology_connecting_source_boundary_cover;
require open emdash.emdash3_2_hom_factor_zero_descent;
require open emdash.emdash3_2_homology_record_cancellation;
require open emdash.emdash3_2_homology_connecting_target_cycles;
require open emdash.emdash3_2_cokernel_monic_factor_descent;
require open emdash.emdash3_2_homology_record_connecting;
require open emdash.emdash3_2_chain_pair_homology_actions;

// The compatibility is read from the existing whole-H cycle factor.
symbol homology_connecting_projection_cone
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
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero))))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB))))
  : τ (@FiberProductCone C P t (@abelian_stability_additive C P t Ab) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) D0 B0 (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) (@computational_chain_pair_d C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero) HB))
≔ @fiber_product_cone_intro C P t (@abelian_stability_additive C P t Ab) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H) D0 B0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
      D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) H) (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) H) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) H) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
      (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
      rowm row0 row1 F G upper_zero) HB)) cf) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@hom_postcomp_factor_path C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) D0
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
      B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) HB) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) (@comp_fapp0 C
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
      B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) HB) B0 D0 (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
      row1 F G upper_zero) HB)) cf);

symbol homology_connecting_projection_cover
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
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero))))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB))))
  : τ (Hom C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
    rowm row0 row1 F G upper_zero) HB) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H))
≔ @computational_fiber_product_lift C P t (@abelian_stability_additive C P t Ab) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H) D0 B0 (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
  row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H) (@computational_chain_pair_d C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_connecting_cover C P t Ab A0 B0 Dm D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
  (@homology_connecting_projection_cone C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero H HB cf);

symbol homology_connecting_projection_cover_cycles
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
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero))))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB))))
  : τ (@= (Hom C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H))
      (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
        C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
        A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
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
        (@homology_connecting_cover_projection C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
        A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
        (@homology_connecting_projection_cover C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero H HB cf))
        (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
        row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) D0
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
        B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) HB) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
        row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) (@comp_fapp0 C
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
        B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) HB) B0 D0 (@computational_chain_pair_d C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) HB)) cf))
≔ @computational_fiber_product_lift_proj1_path C P t (@abelian_stability_additive C P t Ab) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H) D0 B0 (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
  row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H) (@computational_chain_pair_d C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_connecting_cover C P t Ab A0 B0 Dm D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
  (@homology_connecting_projection_cone C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero H HB cf);

symbol homology_connecting_projection_cover_middle
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
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero))))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB))))
  : τ (@= (Hom C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) B0)
      (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
        C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
        A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) B0 (@homology_connecting_cover_middle C P t Ab A0 B0 Dm D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) (@homology_connecting_projection_cover C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G
        upper_zero H HB cf)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB))
≔ @computational_fiber_product_lift_proj2_path C P t (@abelian_stability_additive C P t Ab) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H) D0 B0 (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
  row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H) (@computational_chain_pair_d C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_connecting_cover C P t Ab A0 B0 Dm D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
  (@homology_connecting_projection_cone C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero H HB cf);

symbol homology_connecting_projection_left_zero
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
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero))))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB))))
  : τ (@= (Hom C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) A1) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
    Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) A1
    (@homology_connecting_left_lift C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) H) (@homology_connecting_projection_cover C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero
    H HB cf)) (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0
    B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HB) A1))
≔ @hom_postcomp_factor_paste_zero_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero) HB) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) H) B0 A1 B1
    (@id C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
      rowm row0 row1 F G upper_zero) HB)) (@homology_connecting_cover_middle C P t Ab A0 B0 Dm D0 D1 row0
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) H) (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
      row1 F G upper_zero) HB) (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) (@hom_postcomp_factor_intro C
      (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
      D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) B0
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
      B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) HB) (@homology_connecting_cover_middle C P t Ab A0 B0 Dm D0 D1 row0
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) H) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_connecting_projection_cover C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero H HB cf)
      (@homology_connecting_projection_cover_middle C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero H HB cf))
        (@homology_connecting_left_factor C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) H) (@computational_short_exact_monic C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
      (@computational_short_exact_row_evidence C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
        (@computational_kernel_annihilation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) B0 B1 (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
      (@homology_record_cycles C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) HB));

symbol homology_connecting_projection_target_zero
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
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB))))
  : τ (@= (Hom C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0
    B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HB) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C
    P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
    A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
    row2 G J lower_zero) HT) (@homology_connecting_target_lift C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1 row2 G J
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) lower_zero H HT) (@homology_connecting_projection_cover C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero H HB cf)) (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
    rowm row0 row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)))
≔ @monic_factor_prezero_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G
  J lower_zero) HT) A1 (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t
  Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) A1
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
      A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
      row1 row2 G J lower_zero) HT) (@homology_connecting_left_lift C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
      (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) H) (@id C A1) (@homology_connecting_target_factor C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1
      row2 G J (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
      P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
      rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) lower_zero H HT)
    (@homology_record_cycle_monic C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
      A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
      row2 G J lower_zero) HT)
    (@homology_connecting_projection_cover C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero H HB cf)
      (@homology_connecting_projection_left_zero C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero H HB cf);

symbol homology_connecting_projection_covered_zero
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
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB))))
  : τ (@= (Hom C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) (@comp_fapp0 C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0
    B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) HB) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C
    P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2
    G J lower_zero) HT) (@homology_connecting_covered_homology_map C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1 row2 G J
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero) lower_zero H HT) (@homology_connecting_projection_cover C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero H HB cf)) (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
    rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _ (@comp_assoc C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
      D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
      A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
      row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
      A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
      row2 G J lower_zero) HT) (@homology_connecting_target_lift C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1 row2 G J
      (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) lower_zero H HT) (@homology_connecting_projection_cover C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero H HB cf)))
    (@preadditive_postcompose_zero_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
      B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
      (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
      row2 G J lower_zero) HT) (@homology_record_projection C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
      (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
        C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
        A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
        (@homology_connecting_target_lift C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1 row2 G J
        (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
        rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) lower_zero H HT) (@homology_connecting_projection_cover C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero H HB cf)) (@homology_connecting_projection_target_zero C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2
        rowm row0 row1 row2 F G J upper_zero lower_zero H HT HB cf));

symbol homology_connecting_projection_cycles_zero
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
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB))))
  : τ (@= (Hom C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
    D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT))
      (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
        C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
        A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
        row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
        (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
        row2 G J lower_zero) HT) (@homology_connecting_cycles_map C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1 row2 G J
        (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
        rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) lower_zero H HT) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
        C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
        rowm row0 row1 F G upper_zero) HB)) cf))
      (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
        B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@hom_factor_paste_path C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
        B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) HB) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
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
        row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
        (@id C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
          B1 D1 rowm row0 row1 F G upper_zero) HB)) (@homology_connecting_cover_projection C P t Ab A0 B0 Dm D0 D1 row0
          (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) H) (@id C (@homology_record_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT))
          (@homology_connecting_projection_cover C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero H HB cf)
          (@homology_connecting_covered_homology_map C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1 row2 G J
          (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
          rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero) lower_zero H HT) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
          (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) H) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
          (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
          (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
          rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) H) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C
          P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
          (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
          B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
          (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
          B1 D1 rowm row0 row1 F G upper_zero) HB)) cf) (@homology_connecting_cycles_map C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0
          row1 row2 G J (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) lower_zero H HT)
        (@homology_connecting_projection_cover_cycles C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero H HB cf)
        (@eq_sym _ _ _ (@homology_connecting_cycles_reconstruction C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1 row2 G J
          (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
          rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero) lower_zero H HT))))
    (@homology_connecting_projection_covered_zero C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
      lower_zero H HT HB cf);

symbol homology_record_connecting_projection_zero
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
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1
    F G upper_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB)))) (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C
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
    row1 F G upper_zero)) H) (@homology_record_projection C (@computational_homology_preadditive C P t
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
    row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
    row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
    row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm
    rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
    D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
    row1 F G upper_zero)) H) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
    B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB)) cf))))
  : τ (@= (Hom C (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
    row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT))
      (@comp_fapp0 C (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
        D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
        row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
        (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
        row2 G J lower_zero) HT) (@homology_record_connecting C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
        upper_zero lower_zero H HT) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) (@homology_record_projection C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
        B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
        row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) H) (@homology_record_projection C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
        row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
        (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
        row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) D0
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
        B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) HB) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
        row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) (@comp_fapp0 C
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
        B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero) HB) B0 D0 (@computational_chain_pair_d C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) HB)) cf)) hf))
      (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
        (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
        row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)))
≔ @epic_precomposition_zero_to_zero_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F
  G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
  rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
      row1 F G upper_zero) HB) (@homology_record_projection_epic C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
    (@comp_fapp0 C (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
      Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
      D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
      (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1
      row2 G J lower_zero) HT) (@homology_record_connecting C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
      upper_zero lower_zero H HT) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive
      C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
      row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
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
      row0 row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
      row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0
      D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) H) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) H) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
      (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
      row0 row1 F G upper_zero)) H) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
      (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
      rowm row0 row1 F G upper_zero) HB)) cf)) hf))
    (@eq_trans _ _ _ _
      (@eq_sym _ _ _
        (@hom_factor_paste_path C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
          (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0
          B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
          row0 row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm
          row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
          (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
          (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0
          D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
          (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
          rowm row0 row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
          (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
          (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1
          A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
          row1 row2 G J lower_zero) HT)
          (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
            B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
            Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) (@id C
            (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
            A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
            row0 row1 row2 G J lower_zero) HT)) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
            (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
            (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) H) D0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
            (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
            (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
            t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm
            Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) H) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive
            C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0
            (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
            A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
            (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB)) cf) (@homology_connecting_cycles_map C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm
            row0 row1 row2 G J (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) lower_zero H HT)
            (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
            (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
            B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
            Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
            (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
            Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
            D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
            (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
            row0 row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
            Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
            (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
            D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
            (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
            t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm
            Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) H) (@homology_record_projection C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
            Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
            (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
            Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) D0
            (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P
            t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
            D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) (@comp_fapp0
            C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0 (@computational_chain_pair_d C (@computational_homology_preadditive C
            P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
            (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
            row0 row1 F G upper_zero) HB)) cf)) hf) (@homology_record_connecting C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm
            row0 row1 row2 F G J upper_zero lower_zero H HT)
          (@eq_sym _ _ _ (@hom_precomp_factor_path C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) HB)
            (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm
            B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
            Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
            (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
            Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
            D1 rowm row0 row1 F G upper_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
            (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
            row0 row1 F G upper_zero) HB) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
            Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
            (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm
            D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
            (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
            t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm
            Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
            (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
            rowm row0 row1 F G upper_zero)) H) (@homology_record_projection C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
            Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
            (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
            Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) D0
            (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P
            t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
            D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
            (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
            (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) (@comp_fapp0
            C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
            Ab)) Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0
            A1 B1 D1 rowm row0 row1 F G upper_zero) HB) B0 D0 (@computational_chain_pair_d C (@computational_homology_preadditive C
            P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
            (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_record_cycle_embedding C
            (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B0 B1
            (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
            row0 row1 F G upper_zero) HB)) cf)) hf))
          (@eq_sym _ _ _ (@homology_record_connecting_reconstruction C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1
            row2 F G J upper_zero lower_zero H HT))))
      (@homology_connecting_projection_cycles_zero C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
        lower_zero H HT HB cf));

symbol homology_whole_connecting_projection_zero
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
    (@computational_abelian_preabelian C P t Ab)) KP Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))
    (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))))
      (@comp_fapp0 C (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P
        t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
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
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))) (@fapp0
        (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t
        Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
        (@computational_abelian_preabelian C P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)))
        (@homology_record_connecting C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero
        (@chain_pair_homology_record C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t
        T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
        (@computational_abelian_preabelian C P t Ab)) KP QP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
        D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))
        (@chain_pair_homology_record C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t
        T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
        (@computational_abelian_preabelian C P t Ab)) KP QP A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)))
        (@chain_pair_homology_action C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t
        T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
        (@computational_abelian_preabelian C P t Ab)) KP QP Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
        (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
        (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm
        row0 row1 F G upper_zero)) (@short_exact_row_chain_projection C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0
        B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))
      (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@fapp0
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
        (@computational_abelian_preabelian C P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)))))
≔ @homology_record_connecting_projection_zero C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
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
  (@computational_abelian_preabelian C P t Ab)) KP QP Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))
  (@chain_pair_homology_cycle_action_factor C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP Bm B0 B1 Dm D0 D1 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0
  row1 F G upper_zero)) (@short_exact_row_chain_projection C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
  B1 D1 rowm row0 row1 F G upper_zero)) (@chain_pair_homology_action_factor C (@computational_homology_preadditive C P t
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
