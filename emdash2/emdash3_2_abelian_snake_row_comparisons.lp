/*
  Dependent one-Abelian-capability wrappers at the original structure owner.
  The existing Sigma eliminator exposes PA/normality in the constructor case.
*/
require open emdash.emdash3_2_abelian_structure_elimination;
require open emdash.emdash3_2_snake_row_source_cycle_iso;
require open emdash.emdash3_2_snake_row_target_cokernel_iso;

// The dependent function family fixes the actual Ab-owned endpoints.
symbol SnakeRowSourceCycleComparisonFamily
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  : Grpd
≔ @Pi_grpd (Obj C) (λ A0 : τ _,
      @Pi_grpd (Obj C) (λ B0 : τ _,
      @Pi_grpd (Obj C) (λ D0 : τ _,
      @Pi_grpd (Obj C) (λ A1 : τ _,
      @Pi_grpd (Obj C) (λ B1 : τ _,
      @Pi_grpd (Obj C) (λ D1 : τ _,
      @Pi_grpd (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0) (λ p0 : τ _,
      @Pi_grpd (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A1 B1 D1) (λ p1 : τ _,
      @Pi_grpd (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1) (λ F : τ _,
      @Pi_grpd (@ComputationalShortExactTriple C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 p0) (λ short0 : τ _,
      @Pi_grpd (@ComputationalKernel C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) D0 D1 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1 F)) (λ cycles : τ _,
      (@IsoEvidence C (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) D0 D1 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1 F) cycles) (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) (@short_exact_cokernel_object C P t Ab A0 B0 D0 p0) D1 (@abelian_snake_gamma C P t Ab A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@abelian_snake_gamma_kernel C P t Ab A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1 F)))))))))))))));

symbol abelian_snake_row_source_cycle_iso
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1))
  (short0 : τ (@ComputationalShortExactTriple C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 p0))
  (cycles : τ (@ComputationalKernel C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) D0 D1 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1 F)))
  : τ (@IsoEvidence C (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) D0 D1 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1 F) cycles) (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) (@short_exact_cokernel_object C P t Ab A0 B0 D0 p0) D1 (@abelian_snake_gamma C P t Ab A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@abelian_snake_gamma_kernel C P t Ab A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1 F))))
≔ (@computational_abelian_ind C P t
      (λ Ab0 : τ (@ComputationalAbelianCategory C P t), @SnakeRowSourceCycleComparisonFamily C P t Ab0)
      (λ PA : τ (@PreAbelianCategory C P t),
        λ M : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)), λ E : τ (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)),
          @snake_row_source_cycle_iso C P t PA M E)
      Ab)
    A0 B0 D0 A1 B1 D1 p0 p1 F short0 cycles;

// The dependent function family fixes the actual Ab-owned endpoints.
symbol SnakeRowTargetCokernelComparisonFamily
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  : Grpd
≔ @Pi_grpd (Obj C) (λ A0 : τ _,
      @Pi_grpd (Obj C) (λ B0 : τ _,
      @Pi_grpd (Obj C) (λ D0 : τ _,
      @Pi_grpd (Obj C) (λ A1 : τ _,
      @Pi_grpd (Obj C) (λ B1 : τ _,
      @Pi_grpd (Obj C) (λ D1 : τ _,
      @Pi_grpd (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0) (λ p0 : τ _,
      @Pi_grpd (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A1 B1 D1) (λ p1 : τ _,
      @Pi_grpd (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1) (λ F : τ _,
      @Pi_grpd (@ComputationalShortExactTriple C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 p1) (λ short1 : τ _,
      @Pi_grpd (@ComputationalCokernel C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 A1 (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1 F)) (λ quotient : τ _,
      (@IsoEvidence C (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 (@computational_homology_cycle_object C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 p1 (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 p1)) (@abelian_snake_alpha C P t Ab A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@abelian_snake_alpha_cokernel C P t Ab A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1 F))) (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 A1 (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1 F) quotient)))))))))))));

symbol abelian_snake_row_target_cokernel_iso
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1))
  (short1 : τ (@ComputationalShortExactTriple C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 p1))
  (quotient : τ (@ComputationalCokernel C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 A1 (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1 F)))
  : τ (@IsoEvidence C (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 (@computational_homology_cycle_object C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 p1 (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 p1)) (@abelian_snake_alpha C P t Ab A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@abelian_snake_alpha_cokernel C P t Ab A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1 F))) (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 A1 (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A0 B0 D0 A1 B1 D1 p0 p1 F) quotient))
≔ (@computational_abelian_ind C P t
      (λ Ab0 : τ (@ComputationalAbelianCategory C P t), @SnakeRowTargetCokernelComparisonFamily C P t Ab0)
      (λ PA : τ (@PreAbelianCategory C P t),
        λ M : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)), λ E : τ (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)),
          @snake_row_target_cokernel_iso C P t PA M E)
      Ab)
    A0 B0 D0 A1 B1 D1 p0 p1 F short1 quotient;
