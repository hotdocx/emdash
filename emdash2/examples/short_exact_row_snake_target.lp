/* Isolated owner consumer; unchanged assertions from the combined reviewer. */
require open emdash.emdash3_2_short_exact_row_snake;

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
  (short0 : τ (@ComputationalShortExactTriple C P t PA A0 B0 D0 p0))
  (short1 : τ (@ComputationalShortExactTriple C P t PA A1 B1 D1 p1))
  (quotient : τ (@ComputationalCokernel C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 A1 (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)))
  ⊢ @short_exact_row_target_cokernel_iso C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_intro C P t PA A0 B0 D0 p0 short0) (@computational_short_exact_row_intro C P t PA A1 B1 D1 p1 short1) F quotient
  ≡ @snake_row_target_cokernel_iso C P t PA M E A0 B0 D0 A1 B1 D1 p0 p1 F short1 quotient;
