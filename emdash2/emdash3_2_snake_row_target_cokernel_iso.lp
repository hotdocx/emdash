/*
  Target differential-cokernel isomorphism for the actual snake row map.

  The bottom comparison A1 ⇄ Ker(p1) and alpha = a ∘ next induce the
  cokernel comparison. Its target is the actual supplied Coker(next).
*/
require open emdash.emdash3_2_snake_row_comparisons;
require open emdash.emdash3_2_cokernel_codomain_comparison;

symbol snake_row_target_cokernel_iso
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1))
  (short1 : τ (@ComputationalShortExactTriple C P t PA A1 B1 D1 p1))
  (quotient : τ (@ComputationalCokernel C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 A1 (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)))
  : τ (@IsoEvidence C (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 (@computational_homology_at C P t PA A1 B1 D1 p1)) (@abelian_snake_alpha C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@abelian_snake_alpha_cokernel C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F))) (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 A1 (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F) quotient))
≔ @iso_evidence_sym C (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 A1 (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F) quotient) (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 (@computational_homology_at C P t PA A1 B1 D1 p1)) (@abelian_snake_alpha C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@abelian_snake_alpha_cokernel C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)))
    (@cokernel_codomain_comparison_iso C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 A1 (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 (@computational_homology_at C P t PA A1 B1 D1 p1))
      (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F) (@abelian_snake_alpha C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) quotient (@abelian_snake_alpha_cokernel C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@short_exact_kernel_comparison_iso C P t (@computational_abelian_category_intro C P t PA M E) A1 B1 D1 p1 short1)
      (@snake_row_alpha_comparison_path C P t PA M E A0 B0 D0 A1 B1 D1 p0 p1 F));
