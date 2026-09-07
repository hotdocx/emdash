/*
  Source-cycle isomorphism for the actual snake associated with a row map.

  The top short-exact comparison Coker(i0) ⇄ D0 and gamma = prev ∘ q
  induce the kernel comparison. The supplied cycles are the actual kernel
  intended by the homology consumer; they are not replaced by a new choice.
*/
require open emdash.emdash3_2_snake_row_comparisons;
require open emdash.emdash3_2_kernel_domain_comparison;
require open emdash.emdash3_2_short_exact_cokernel_comparison;

symbol snake_row_source_cycle_iso
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
  (short0 : τ (@ComputationalShortExactTriple C P t PA A0 B0 D0 p0))
  (cycles : τ (@ComputationalKernel C (@additive_preadditive C P t (@preabelian_additive C P t PA)) D0 D1 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)))
  : τ (@IsoEvidence C (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t PA)) D0 D1 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F) cycles) (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@short_exact_cokernel_object C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0) D1 (@abelian_snake_gamma C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@abelian_snake_gamma_kernel C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F))))
≔ @iso_evidence_sym C (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@short_exact_cokernel_object C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0) D1 (@abelian_snake_gamma C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@abelian_snake_gamma_kernel C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F))) (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t PA)) D0 D1 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F) cycles)
    (@kernel_domain_comparison_iso C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@short_exact_cokernel_object C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0) D0 D1
      (@abelian_snake_gamma C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F) (@abelian_snake_gamma_kernel C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) cycles (@short_exact_cokernel_comparison_iso C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0 short0)
      (@snake_row_gamma_comparison_path C P t PA M E A0 B0 D0 A1 B1 D1 p0 p1 F));
