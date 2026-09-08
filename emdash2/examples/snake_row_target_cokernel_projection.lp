/* The inverse row comparison reconstructs the original quotient projection. */
require open emdash.emdash3_2_snake_row_target_cokernel_projection;

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
  (short1 : τ (@ComputationalShortExactTriple C P t PA A1 B1 D1 p1))
  (quotient : τ (@ComputationalCokernel C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 A1 (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)))
  ⊢ @snake_row_target_cokernel_from_projection_path C P t PA M E A0 B0 D0 A1 B1 D1 p0 p1 F short1 quotient
    : τ (@= (Hom C A1 (@abelian_snake_coker_alpha_object C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)))
      (@comp_fapp0 C A1 (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 A1 (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F) quotient) (@abelian_snake_coker_alpha_object C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@iso_evidence_from C (@abelian_snake_coker_alpha_object C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 A1 (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F) quotient) (@snake_row_target_cokernel_iso C P t PA M E A0 B0 D0 A1 B1 D1 p0 p1 F short1 quotient)) (@computational_cokernel_morphism C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 A1 (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F) quotient))
      (@comp_fapp0 C A1 (@abelian_snake_ker_lambda_object C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@abelian_snake_coker_alpha_object C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@abelian_snake_pi C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@iso_evidence_to C A1 (@abelian_snake_ker_lambda_object C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@short_exact_kernel_comparison_iso C P t (@computational_abelian_category_intro C P t PA M E) A1 B1 D1 p1 short1))));
