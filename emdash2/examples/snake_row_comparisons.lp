/* Isolated owner consumer; unchanged assertions from the combined reviewer. */
require open emdash.emdash3_2_snake_row_comparisons;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1))
  ⊢ @snake_row_gamma_comparison_path C P t PA M E A0 B0 D0 A1 B1 D1 p0 p1 F
  : τ (@= (Hom C (@short_exact_cokernel_object C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0) D1) (@abelian_snake_gamma C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@comp_fapp0 C (@short_exact_cokernel_object C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0) D0 D1 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F) (@short_exact_cokernel_comparison C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0)));


assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1))
  ⊢ @snake_row_alpha_comparison_path C P t PA M E A0 B0 D0 A1 B1 D1 p0 p1 F
  : τ (@= (Hom C A0 (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 (@computational_homology_at C P t PA A1 B1 D1 p1))) (@abelian_snake_alpha C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@comp_fapp0 C A0 A1 (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 (@computational_homology_at C P t PA A1 B1 D1 p1)) (@short_exact_kernel_comparison C P t (@computational_abelian_category_intro C P t PA M E) A1 B1 D1 p1) (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)));


assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1))
  ⊢ @abelian_snake_delta_cokernel C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F) ≡ (@short_exact_incoming_cokernel C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0);


assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1))
  ⊢ (@abelian_snake_mu C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) ≡ @computational_homology_cycle_embedding C P t PA A1 B1 D1 p1 (@computational_homology_at C P t PA A1 B1 D1 p1);
