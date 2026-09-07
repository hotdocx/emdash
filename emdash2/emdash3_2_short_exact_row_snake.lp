/*
  Whole short-exact-row usability view of the existing internal row maps.

  Pair and short-exact evidence are projections of the supplied whole rows.
  The snake and endpoint comparisons reuse the already-checked constructors.
*/
require open emdash.emdash3_2_short_exact_rows;
require open emdash.emdash3_2_abelian_snake_row_comparisons;

// Transparent alias: the map is the existing map between the actual row pairs.
symbol ShortExactRowMap
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (r0 : τ (@ComputationalShortExactRow C P t PA A0 B0 D0))
  (r1 : τ (@ComputationalShortExactRow C P t PA A1 B1 D1))
  : Grpd
≔ @ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1);

symbol short_exact_row_map_snake_triple
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (r0 : τ (@ComputationalShortExactRow C P t PA A0 B0 D0))
  (r1 : τ (@ComputationalShortExactRow C P t PA A1 B1 D1))
  (F : τ (@ShortExactRowMap C P t PA A0 B0 D0 A1 B1 D1 r0 r1))
  : τ (@AbelianSnakeTriple C (@computational_homology_preadditive C P t PA) A0 B0 B1 D1)
≔ @chain_pair_map_snake_triple C (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F;

symbol short_exact_row_source_cycle_iso
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (r0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (r1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (F : τ (@ShortExactRowMap C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 r0 r1))
  (cycles : τ (@ComputationalKernel C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) D0 D1 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 r0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 r1) F)))
  : τ (@IsoEvidence C (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) D0 D1 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 r0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 r1) F) cycles) (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) (@short_exact_cokernel_object C P t Ab A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 r0)) D1 (@abelian_snake_gamma C P t Ab A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 r0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 r1) F)) (@abelian_snake_gamma_kernel C P t Ab A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 r0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 r1) F))))
≔ @abelian_snake_row_source_cycle_iso C P t Ab A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 r0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 r1) F
    (@computational_short_exact_row_evidence C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 r0) cycles;

symbol short_exact_row_target_cokernel_iso
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (r0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (r1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (F : τ (@ShortExactRowMap C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 r0 r1))
  (quotient : τ (@ComputationalCokernel C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 A1 (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 r0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 r1) F)))
  : τ (@IsoEvidence C (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 (@computational_homology_cycle_object C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 r1) (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 r1))) (@abelian_snake_alpha C P t Ab A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 r0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 r1) F)) (@abelian_snake_alpha_cokernel C P t Ab A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 r0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 r1) F))) (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 A1 (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 r0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 r1) F) quotient))
≔ @abelian_snake_row_target_cokernel_iso C P t Ab A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 r0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 r1) F
    (@computational_short_exact_row_evidence C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 r1) quotient;
