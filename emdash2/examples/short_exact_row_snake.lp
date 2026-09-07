/* Whole-row source computation and owner typing, retaining the original assertions. */
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
  ⊢ F : τ (@ShortExactRowMap C P t PA A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_intro C P t PA A0 B0 D0 p0 short0) (@computational_short_exact_row_intro C P t PA A1 B1 D1 p1 short1));


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
  ⊢ @short_exact_row_map_snake_triple C P t PA A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_intro C P t PA A0 B0 D0 p0 short0) (@computational_short_exact_row_intro C P t PA A1 B1 D1 p1 short1) F
  ≡ (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F);


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
  (cycles : τ (@ComputationalKernel C (@additive_preadditive C P t (@preabelian_additive C P t PA)) D0 D1 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)))
  ⊢ @short_exact_row_source_cycle_iso C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_intro C P t PA A0 B0 D0 p0 short0) (@computational_short_exact_row_intro C P t PA A1 B1 D1 p1 short1) F cycles
  ≡ @snake_row_source_cycle_iso C P t PA M E A0 B0 D0 A1 B1 D1 p0 p1 F short0 cycles;


assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (r0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (r1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (F : τ (@ShortExactRowMap C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 r0 r1))
  (cycles : τ (@ComputationalKernel C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) D0 D1 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 r0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 r1) F)))
  ⊢ @short_exact_row_source_cycle_iso C P t Ab A0 B0 D0 A1 B1 D1 r0 r1 F cycles
  : τ (@IsoEvidence C (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) D0 D1 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 r0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 r1) F) cycles) (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) (@short_exact_cokernel_object C P t Ab A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 r0)) D1 (@abelian_snake_gamma C P t Ab A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 r0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 r1) F)) (@abelian_snake_gamma_kernel C P t Ab A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 r0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 r1) F))));


assertnot
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (r0 : τ (@ComputationalShortExactRow C P t PA A0 B0 D0))
  (r1 : τ (@ComputationalShortExactRow C P t PA A1 B1 D1))
  (other : τ (@ComputationalShortExactRow C P t PA A1 B1 D1))
  (F : τ (@ShortExactRowMap C P t PA A0 B0 D0 A1 B1 D1 r0 other))
  ⊢ @short_exact_row_map_snake_triple C P t PA A0 B0 D0 A1 B1 D1 r0 r1 F
  : τ (@AbelianSnakeTriple C (@computational_homology_preadditive C P t PA) A0 B0 B1 D1);
