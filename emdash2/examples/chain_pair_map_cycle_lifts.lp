/* Selected-kernel cycle lifting through a chain-pair map. */

require open emdash.emdash3_2_chain_pair_map_cycle_lifts;

// A downstream consumer gets a factor point through that actual embedding.
assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  (lower_monic : τ (@IsMonic C D0 D1 (@computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 F)))
  (T : τ (Obj C))
  (test : τ (Hom C T A1))
  (factor : τ (@HomPostcompFactor C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@comp_fapp0 C T A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1) test)))
  (K : τ (@ComputationalKernel C S B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0)))
  ⊢ @hom_postcomp_factor_intro C (@computational_kernel_object C S B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0) K) B0 T (@computational_kernel_morphism C S B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0) K) (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@comp_fapp0 C T A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1) test) factor)
      (@chain_pair_map_factor_cycle_lift C S A0 B0 D0 A1 B1 D1 p0 p1 F lower_monic T test factor K) (@chain_pair_map_factor_cycle_lift_path C S A0 B0 D0 A1 B1 D1 p0 p1 F lower_monic T test factor K)
  : τ (@HomPostcompFactor C (@computational_kernel_object C S B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0) K) B0 T (@computational_kernel_morphism C S B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0) K) (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@comp_fapp0 C T A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1) test) factor));

// A second kernel choice cannot silently replace the selected lift's target.
assertnot
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  (lower_monic : τ (@IsMonic C D0 D1 (@computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 F)))
  (T : τ (Obj C))
  (test : τ (Hom C T A1))
  (factor : τ (@HomPostcompFactor C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@comp_fapp0 C T A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1) test)))
  (K : τ (@ComputationalKernel C S B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0)))
  (Kother : τ (@ComputationalKernel C S B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0)))
  ⊢ (@chain_pair_map_factor_cycle_lift C S A0 B0 D0 A1 B1 D1 p0 p1 F lower_monic T test factor K)
  : τ (Hom C T (@computational_kernel_object C S B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0) Kother));
