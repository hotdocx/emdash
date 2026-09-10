/*
  Exactness at H(A') in the retained whole-H window.
  A covered H(i')-kernel test gives a middle-boundary preimage. Its original
  row quotient lifts to the retained source cycles and the original connecting
  pullback. Row/cycle monicity identifies the target lift; delta reconstruction
  supplies all-test covers. No H reselection, object transport or new rule.
*/
require open emdash.emdash3_2_homology_connecting_inclusion_zero;
require open emdash.emdash3_2_homology_map_kernel_covers;
require open emdash.emdash3_2_exactness_covers;
require open emdash.emdash3_2_homology_window;

/* Third interior: a covered inclusion-kernel test has a middle boundary. */

symbol homology_third_boundary_reconstruction [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT))))
  (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf))))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf)) hf) T))
  : τ (@= (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P
    t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) B1) (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab
    A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
    (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@homology_map_kernel_cover_boundary C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test)) (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0
    A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
    (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) A1 B1 (@computational_chain_pair_dnext C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
    (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C
    P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 (@homology_record_cycle_embedding C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_map_kernel_cover_cycles C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test))))
≔ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@hom_postcomp_factor_path C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P
  t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) B0 B1 (@computational_chain_pair_map_middle C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
  (@homology_map_kernel_cover_boundary C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test)) (@homology_record_boundary_multiple C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_map_kernel_cover_boundary C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test)))) (@eq_trans _ _ _ _ (@eq_ap (Hom C
  (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB)) (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) B1) (λ h : τ (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)), (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0
  A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
  (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) h)) _ _
  (@homology_map_kernel_cover_target_path C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test)) (@eq_trans _ _ _ _ (@comp_assoc C
  (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) (@homology_map_kernel_cover_cycles C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test)) (@eq_trans _ _ _ _ (@eq_ap (Hom C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) B1) (Hom
  C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) B1) (λ h : τ (Hom C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) B1), (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) B1 h (@homology_map_kernel_cover_cycles C P t Ab A0 A1 A2 B0 B1
  B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test))) _ _ (@hom_postcomp_factor_path C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf)) (@eq_sym _ _ _ (@comp_assoc C (@homology_map_kernel_cover_object C P t Ab
  A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
  (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_map_kernel_cover_cycles C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test)))))));

/* The covered boundary projects to a cycle in the quotient column. */

symbol homology_third_projected_boundary_zero [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT))))
  (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf))))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf)) hf) T))
  : τ (@= (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P
    t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) D1) (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab
    A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
    (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) D0 D1 (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C
    P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) B0 D0 (@computational_chain_pair_d C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_map_kernel_cover_boundary C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test))) (@preadditive_hom_zero C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
    Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf
    T test) D1))
≔ (@eq_trans _ _ _ _ (@comp_assoc C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) B0 D0 D1 (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) (@computational_chain_pair_d C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
  (@homology_map_kernel_cover_boundary C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test)) (@eq_trans _ _ _ _ (@eq_ap (Hom C B0 D1) (Hom C
  (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) D1) (λ h : τ (Hom C B0 D1), (@comp_fapp0 C
  (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) B0 D1 h (@homology_map_kernel_cover_boundary C P t Ab A0 A1 A2 B0
  B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2
  D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test))) _ _ (@computational_chain_pair_map_lower_path C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc C
  (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) B0 B1 D1 (@computational_chain_pair_d C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
  (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) (@homology_map_kernel_cover_boundary C P t Ab A0 A1
  A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
  A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian
  C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test))) (@eq_trans _ _ _ _ (@eq_ap (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) B1) (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C
  P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) D1) (λ h : τ (Hom C (@homology_map_kernel_cover_object C P t Ab
  A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
  (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) B1), (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab
  A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
  (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) B1 D1 (@computational_chain_pair_d C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) h)) _ _
  (@homology_third_boundary_reconstruction C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
  upper_zero lower_zero H HT HB cf hf T test)) (@eq_trans _ _ _ _ (@comp_assoc C (@homology_map_kernel_cover_object C
  P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0
  B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
  (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) A1 B1 D1 (@computational_chain_pair_d C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_map_kernel_cover_cycles C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test))) (@preadditive_precompose_zero_path C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) A1 D1 (@comp_fapp0 C A1 B1 D1 (@computational_chain_pair_d C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@computational_chain_pair_dnext C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)))
  (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P
  t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_map_kernel_cover_cycles C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test)) (@computational_chain_pair_path C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))))))));

symbol homology_third_source_cycle_test [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT))))
  (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf))))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf)) hf) T))
  : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) D0 D1 (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) (@homology_map_kernel_cover_object C P t Ab A0 A1
    A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
    D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
    (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test))
≔ @Struct_sigma (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) D0)
  (λ h : τ (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C
    P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) D0), @= (Hom C (@homology_map_kernel_cover_object C P t Ab A0
    A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
    (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) D1) (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab
    A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
    (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) D0 D1 (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) h)
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) D1))
  (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P
    t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) B0 D0 (@computational_chain_pair_d C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_map_kernel_cover_boundary C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test)) (@homology_third_projected_boundary_zero C P t Ab Am Bm Dm A0
    B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero H HT HB cf hf T test);

/* Retain the source cycles and enter the original connecting cover. */

symbol homology_third_source_cycle [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT))))
  (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf))))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf)) hf) T))
  : τ (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H))
≔ @computational_kernel_lift C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) D0 D1 (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) (@homology_record_cycles C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero)) H) (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_third_source_cycle_test C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
  upper_zero lower_zero H HT HB cf hf T test);

symbol homology_third_source_cycle_reconstruction [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT))))
  (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf))))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf)) hf) T))
  : τ (@= (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P
    t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) D0) (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab
    A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
    (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) D0
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_third_source_cycle C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
    lower_zero H HT HB cf hf T test)) (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
    Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf
    T test) B0 D0 (@computational_chain_pair_d C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_map_kernel_cover_boundary C P t Ab A0 A1
    A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
    D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
    (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test)))
≔ @computational_kernel_lift_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) D0 D1 (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) (@homology_record_cycles C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero)) H) (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_third_source_cycle_test C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
  upper_zero lower_zero H HT HB cf hf T test);

symbol homology_third_connecting_cone [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT))))
  (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf))))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf)) hf) T))
  : τ (@FiberProductCone C P t (@abelian_stability_additive C P t Ab) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) D0 B0
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)) (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test))
≔ @fiber_product_cone_intro C P t (@abelian_stability_additive C P t Ab) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero)) H) D0 B0 (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
  D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
  (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0)) (@homology_third_source_cycle C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
  upper_zero lower_zero H HT HB cf hf T test) (@homology_map_kernel_cover_boundary C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_third_source_cycle_reconstruction C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2
  F G J upper_zero lower_zero H HT HB cf hf T test);

symbol homology_third_connecting_lift [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT))))
  (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf))))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf)) hf) T))
  : τ (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H))
≔ @computational_fiber_product_lift C P t (@abelian_stability_additive C P t Ab) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero)) H) D0 B0 (@homology_record_cycle_embedding C (@computational_homology_preadditive
  C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
  A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
  (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0)) (@homology_connecting_cover C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0
  D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
  (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_third_connecting_cone C P t Ab Am Bm Dm A0 B0 D0 A1 B1
  D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero H HT HB cf hf T test);

symbol homology_third_connecting_source_path [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT))))
  (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf))))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf)) hf) T))
  : τ (@= (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P
    t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H))
    (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C
    P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_connecting_cover_projection C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab
    A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_third_connecting_lift C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
    lower_zero H HT HB cf hf T test)) (@homology_third_source_cycle C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm
    row0 row1 row2 F G J upper_zero lower_zero H HT HB cf hf T test))
≔ @computational_fiber_product_lift_proj1_path C P t (@abelian_stability_additive C P t Ab)
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) D0 B0 (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero)) H) (@computational_chain_pair_d C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_connecting_cover C P t Ab A0 B0 Dm D0 D1
  row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_third_connecting_cone C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
  upper_zero lower_zero H HT HB cf hf T test);

symbol homology_third_connecting_middle_path [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT))))
  (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf))))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf)) hf) T))
  : τ (@= (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P
    t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) B0) (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab
    A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
    (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) B0
    (@homology_connecting_cover_middle C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0
    B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_third_connecting_lift C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
    lower_zero H HT HB cf hf T test)) (@homology_map_kernel_cover_boundary C P t Ab A0 A1 A2 B0 B1 B2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
    Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf
    T test))
≔ @computational_fiber_product_lift_proj2_path C P t (@abelian_stability_additive C P t Ab)
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) D0 B0 (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero)) H) (@computational_chain_pair_d C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_connecting_cover C P t Ab A0 B0 Dm D0 D1
  row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_third_connecting_cone C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
  upper_zero lower_zero H HT HB cf hf T test);

/* Original monomorphisms identify the connecting lift with the covered cycle. */

symbol homology_third_connecting_left_path [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT))))
  (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf))))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf)) hf) T))
  : τ (@= (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P
    t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) A1) (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab
    A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
    (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) A1
    (@homology_connecting_left_lift C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
    (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1
    B1 D1 rowm row0 row1 F G upper_zero) H) (@homology_third_connecting_lift C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2
    D2 rowm row0 row1 row2 F G J upper_zero lower_zero H HT HB cf hf T test)) (@comp_fapp0 C
    (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 (@homology_record_cycle_embedding C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_map_kernel_cover_cycles C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test)))
≔ (@computational_short_exact_monic C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
  (@computational_short_exact_row_evidence C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
  (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1
  A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
  A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian
  C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab
  A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) A1
  (@homology_connecting_left_lift C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero) H) (@homology_third_connecting_lift C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2
  rowm row0 row1 row2 F G J upper_zero lower_zero H HT HB cf hf T test)) (@comp_fapp0 C
  (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_map_kernel_cover_cycles C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test)) (@eq_trans _ _ _ _ (@comp_assoc C
  (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero)) H) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive
  C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_connecting_left_lift C P t Ab A0 B0 D0 A1 B1
  D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) H)
  (@homology_third_connecting_lift C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
  lower_zero H HT HB cf hf T test)) (@eq_trans _ _ _ _ (@eq_ap (Hom C (@homology_connecting_cover_object C P t Ab A0
  B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) B1) (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1
  B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) B1) (λ k : τ (Hom C (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero)) H) B1), (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1
  B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab
  A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) B1 k
  (@homology_third_connecting_lift C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
  lower_zero H HT HB cf hf T test))) _ _ (@homology_connecting_left_reconstruction C P t Ab A0 B0 D0 A1 B1 D1 Dm row0
  row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) H))
  (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab
  A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) B0 B1
  (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) (@homology_connecting_cover_middle C P t Ab A0 B0 Dm
  D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) (@homology_third_connecting_lift C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1
  A2 B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero H HT HB cf hf T test))) (@eq_trans _ _ _ _ (@eq_ap (Hom C
  (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) B0) (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2
  B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
  B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C
  P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) B1) (λ k : τ (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) B0), (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) B0 B1 (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) k)) _ _ (@homology_third_connecting_middle_path C P t
  Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero H HT HB cf hf T test))
  (@homology_third_boundary_reconstruction C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
  upper_zero lower_zero H HT HB cf hf T test)))));

symbol homology_third_connecting_target_path [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT))))
  (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf))))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf)) hf) T))
  : τ (@= (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P
    t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
    Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf
    T test) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P
    t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_connecting_target_lift C P t Ab A0 B0 D0 A1 B1 D1 A2
    B2 D2 Dm row0 row1 row2 G J (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) lower_zero
    H HT) (@homology_third_connecting_lift C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
    upper_zero lower_zero H HT HB cf hf T test)) (@homology_map_kernel_cover_cycles C P t Ab A0 A1 A2 B0 B1 B2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
    Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf
    T test))
≔ (@homology_record_cycle_monic C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab
  A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_connecting_target_lift C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2
  Dm row0 row1 row2 G J (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) lower_zero H
  HT) (@homology_third_connecting_lift C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
  upper_zero lower_zero H HT HB cf hf T test)) (@homology_map_kernel_cover_cycles C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@eq_trans _ _ _ _ (@comp_assoc C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab
  A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_connecting_target_lift C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0
  row1 row2 G J (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) lower_zero H
  HT) (@homology_third_connecting_lift C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
  upper_zero lower_zero H HT HB cf hf T test)) (@eq_trans _ _ _ _ (@eq_ap (Hom C (@homology_connecting_cover_object C
  P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) A1) (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1
  B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) A1) (λ k : τ (Hom C (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero)) H) A1), (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1
  B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab
  A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) A1 k
  (@homology_third_connecting_lift C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
  lower_zero H HT HB cf hf T test))) _ _ (@homology_connecting_target_reconstruction C P t Ab A0 B0 D0 A1 B1 D1 A2 B2
  D2 Dm row0 row1 row2 G J (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero) lower_zero H
  HT)) (@homology_third_connecting_left_path C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
  upper_zero lower_zero H HT HB cf hf T test)));

/* Covered delta-preimages at the original homology objects. */

symbol homology_third_homology_reconstruction [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT))))
  (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf))))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf)) hf) T))
  : τ (@= (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P
    t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT))
    (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C
    P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0
    D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_connecting C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1
    A2 B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero H HT) (@comp_fapp0 C (@homology_map_kernel_cover_object C
    P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0
    B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
    (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_third_source_cycle C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
    lower_zero H HT HB cf hf T test))) (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
    Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf
    T test) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_map_kernel_cover_cycles C P t Ab A0 A1 A2 B0 B1 B2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
    Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf
    T test)))
≔ (@eq_trans _ _ _ _ (@eq_ap (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)) (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) (λ c : τ (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2
  B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
  B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C
  P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)), (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2
  B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
  B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C
  P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_connecting C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
  lower_zero H HT) (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
  D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
  (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) c))) _ _ (@eq_sym _ _ _ (@homology_third_connecting_source_path C P t
  Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero H HT HB cf hf T test)))
  (@eq_trans _ _ _ _ (@eq_ap (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)) (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) (λ k : τ (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2
  B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
  B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C
  P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)), (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2
  B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
  B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C
  P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_connecting C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
  lower_zero H HT) k)) _ _ (@comp_assoc C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab
  A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
  D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
  (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) (@homology_connecting_cover_projection C P t Ab A0 B0 Dm D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero)) H) (@homology_third_connecting_lift C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2
  rowm row0 row1 row2 F G J upper_zero lower_zero H HT HB cf hf T test))) (@eq_trans _ _ _ _ (@comp_assoc C
  (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
  D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
  B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_connecting C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2
  rowm row0 row1 row2 F G J upper_zero lower_zero H HT) (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A0
  B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) (@homology_record_cycle_object C (@computational_homology_preadditive
  C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
  A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) (@homology_record_projection C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
  A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
  (@homology_connecting_cover_projection C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab
  A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H))
  (@homology_third_connecting_lift C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
  lower_zero H HT HB cf hf T test)) (@eq_trans _ _ _ _ (@eq_ap (Hom C (@homology_connecting_cover_object C P t Ab A0
  B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) (Hom C
  (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_object C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) (λ k : τ
  (Hom C (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t
  Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
  B2 D2 row0 row1 row2 G J lower_zero) HT)), (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1
  B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab
  A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
  B2 D2 row0 row1 row2 G J lower_zero) HT) k (@homology_third_connecting_lift C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2
  B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero H HT HB cf hf T test))) _ _
  (@homology_record_connecting_covered_reconstruction C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2
  F G J upper_zero lower_zero H HT)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc C
  (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_connecting_cover_object C P t Ab A0 B0 Dm D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero)) H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
  B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_projection C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_connecting_target_lift C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 Dm row0 row1 row2 G J
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero) lower_zero H HT) (@homology_third_connecting_lift C P t Ab Am Bm Dm A0 B0
  D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero H HT HB cf hf T test))) (@eq_ap (Hom C
  (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) (λ k : τ (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2
  B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
  B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C
  P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)), (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0
  A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
  (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) k)) _ _ (@homology_third_connecting_target_path C P t Ab Am Bm Dm A0
  B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero H HT HB cf hf T test)))))));

symbol homology_third_covered_preimage_path [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT))))
  (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf))))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf)) hf) T))
  : τ (@= (Hom C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P
    t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT))
    (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C
    P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0
    D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_connecting C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1
    A2 B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero H HT) (@comp_fapp0 C (@homology_map_kernel_cover_object C
    P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0
    B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
    (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_third_source_cycle C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
    lower_zero H HT HB cf hf T test))) (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
    Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf
    T test) T (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@weak_kernel_annihilator_arrow C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf)) hf) T test) (@homology_map_kernel_cover_epi C P t Ab A0 A1 A2 B0 B1 B2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
    Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf
    T test)))
≔ @eq_trans _ _ _ _ (@homology_third_homology_reconstruction C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0
  row1 row2 F G J upper_zero lower_zero H HT HB cf hf T test) (@homology_map_kernel_cover_source_path C P t Ab A0 A1
  A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
  A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian
  C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test);

/* All-test covers prove the existing third-pair exactness predicate. */

symbol homology_record_third_window_pair [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT))))
  (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf))))
  : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB))
≔ @computational_chain_pair_intro C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
  B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_connecting C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2
  rowm row0 row1 row2 F G J upper_zero lower_zero H HT) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
  B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf)) hf)
    (@homology_record_connecting_inclusion_zero C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
      upper_zero lower_zero H HT HB cf hf);

symbol homology_third_cover [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT))))
  (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf))))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P
    t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf)) hf) T))
  : τ (@ComputationalExactCoverWitness C P t (@computational_abelian_preabelian C P t Ab) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_third_window_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
    upper_zero lower_zero H HT HB cf hf) T test)
≔ @computational_exact_cover_intro C P t (@computational_abelian_preabelian C P t Ab) (@homology_record_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
  B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_third_window_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2
  B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero H HT HB cf hf) T test (@homology_map_kernel_cover_object C P t
  Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB
  (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf) hf T test) (@homology_map_kernel_cover_epi C P t Ab A0 A1 A2 B0 B1 B2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t
  Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
  row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf) hf T
  test)
    (@homology_map_kernel_cover_is_epic C P t Ab A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2
      D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2
      D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C
      P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
      (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
      (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
      (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
      C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1
      B1 D1 row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf)
      hf T test) (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 A1 A2 B0 B1 B2
      (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2
      D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C
      P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT HB (@hom_postcomp_factor_arrow C
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
      P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
      D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
      (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2
      D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C (@computational_homology_preadditive C
      P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
      (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) A1 B1
      (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
      C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1
      B1 D1 row1)) (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)) cf)
      hf T test) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
      A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
      Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
      (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
      t Ab)) Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
      (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
      (@homology_third_source_cycle C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
      lower_zero H HT HB cf hf T test))
    (@homology_third_covered_preimage_path C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
      upper_zero lower_zero H HT HB cf hf T test);

symbol homology_third_covers [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT))))
  (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf))))
  : τ (@HasComputationalExactCovers C P t (@computational_abelian_preabelian C P t Ab) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_third_window_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
    upper_zero lower_zero H HT HB cf hf))
≔ λ T : τ (Obj C), λ test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
  B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
  B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
  (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1
  D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
  (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
  B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero) HT)) cf)) hf) T),
    @homology_third_cover C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero
      H HT HB cf hf T test;

symbol homology_record_third_exact [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (HT : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (HB : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1
    A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) B1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT))))
  (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2
    (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HB) B1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB) (@comp_fapp0 C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_record_cycle_embedding C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 A1 A2
    (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
    row0 row1 row2 G J lower_zero) HT)) cf))))
  (HW : τ (@ComputationalHomologyAt C P t (@computational_abelian_preabelian C P t Ab) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_third_window_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
    upper_zero lower_zero H HT HB cf hf)))
  : τ (@ComputationalExactAt C P t (@computational_abelian_preabelian C P t Ab) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)) H)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1
    B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT) (@homology_record_object C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HB)
    (@homology_record_third_window_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
    upper_zero lower_zero H HT HB cf hf) HW)
≔ @computational_exact_at_from_covers C P t (@computational_abelian_preabelian C P t Ab) (@homology_record_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Dm D0 D1
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero)) H) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) HT)
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  B0 B1 B2 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2
  B2 D2 row0 row1 row2 G J lower_zero) HB) (@homology_record_third_window_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2
  B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero H HT HB cf hf) HW (@homology_third_covers C P t Ab Am Bm Dm A0
  B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero H HT HB cf hf);

/* Third exactness uses literal whole-H objects, its action, and the existing delta. */

symbol homology_whole_window_third_covers [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  : τ (@HasComputationalExactCovers C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P
    t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C
    P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))) (@fapp0
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P
    t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C
    P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)))
    (@homology_whole_window_third_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
    upper_zero lower_zero C1 T T0 KP QP))
≔ @homology_third_covers C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero
  (@chain_pair_homology_record C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
  A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))
  (@chain_pair_homology_record C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP A0 A1 A2 (@short_exact_row_chain_source_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))
  (@chain_pair_homology_record C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))
  (@chain_pair_homology_cycle_action_factor C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t
  Ab)) KP QP A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab)
  A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_inclusion C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
  row1 row2 G J lower_zero)) (@chain_pair_homology_action_factor C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t
  Ab)) KP QP A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab)
  A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero) (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)
  (@short_exact_row_chain_inclusion C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0
  row1 row2 G J lower_zero));

symbol homology_whole_window_third_exact [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  : τ (@ComputationalExactAt C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0
    B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))) (@fapp0
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P
    t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C
    P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)))
    (@homology_whole_window_third_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
    upper_zero lower_zero C1 T T0 KP QP) (@computational_homology_at C P t (@computational_abelian_preabelian C P t
    Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P
    t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C
    P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))) (@fapp0
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P
    t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C
    P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)))
    (@homology_whole_window_third_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
    upper_zero lower_zero C1 T T0 KP QP)))
≔ @computational_exact_at_from_covers C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C
  t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t
  Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero)))) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
  (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian
  C P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
  D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P
  t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive
  C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (@homology_whole_window_third_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
  lower_zero C1 T T0 KP QP) (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t
  Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)
  (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1
  D1 rowm row0 row1 F G upper_zero)))) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
  (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian
  C P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
  D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P
  t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive
  C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (@homology_whole_window_third_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
  lower_zero C1 T T0 KP QP))
    (@homology_whole_window_third_covers C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
      upper_zero lower_zero C1 T T0 KP QP);
