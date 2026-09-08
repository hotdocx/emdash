/* The actual upper differential factors through the selected beta kernel. */
require open emdash.emdash3_2_abelian_snake_six_term_kernel_beta_foundation;
require open emdash.emdash3_2_chain_pair_map_snake;
require open emdash.emdash3_2_short_exact_row_chain_projection;

symbol snake_row_source_upper_factor
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)))
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (r0 : τ (@ComputationalShortExactRow C P t PA A0 B0 D0))
  (r1 : τ (@ComputationalShortExactRow C P t PA A1 B1 D1))
  (r2 : τ (@ComputationalShortExactRow C P t PA A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1)))
  (G : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2)))
  (middle_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G) (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F))
    (@preadditive_hom_zero C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B0 B2)))
  : τ (@HomPostcompFactor C (@abelian_snake_ker_beta_object C P t (@computational_abelian_category_intro C P t PA M E) A1 B1 B2 D2 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G)) B1 B0 (@abelian_snake_k_beta C P t (@computational_abelian_category_intro C P t PA M E) A1 B1 B2 D2 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G)) (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F))
≔ is_contr_center (@computational_kernel_factor_contr C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B1 B2 (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G) (@abelian_snake_beta_kernel C P t (@computational_abelian_category_intro C P t PA M E) A1 B1 B2 D2 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G)) B0
    (@computational_chain_pair_cone C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B0 B1 B2 (@short_exact_row_chain_middle_pair C P t PA A0 B0 D0 A1 B1 D1 A2 B2 D2 r0 r1 r2 F G middle_zero)));
