/*
  A factor of the target incoming differential through a chain-pair map's
  middle component lies in source cycles when the lower component is monic.
  The supplied whole source kernel remains the owner of the resulting lift.
*/
require open emdash.emdash3_2_chain_pair_maps;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

// lower(F) o d0 o r = d1 o middle(F) o r = d1 o dnext1 o test = 0.
symbol chain_pair_map_factor_cycle_zero_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  (lower_monic : τ (@IsMonic C D0 D1 (@computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 F)))
  (T : τ (Obj C))
  (test : τ (Hom C T A1))
  (factor : τ (@HomPostcompFactor C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@comp_fapp0 C T A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1) test)))
  : τ (@= (Hom C T D0)
      (@comp_fapp0 C T B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0) (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@comp_fapp0 C T A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1) test) factor))
      (@preadditive_hom_zero C S T D0))
≔ @monic_postcomposition_zero_to_zero_path C S T D0 D1
    (@computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 F) lower_monic
    (@comp_fapp0 C T B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0) (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@comp_fapp0 C T A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1) test) factor))
    (@eq_trans _ _ _ _
      (@comp_assoc C T B0 D0 D1 (@computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@computational_chain_pair_d C S A0 B0 D0 p0) (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@comp_fapp0 C T A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1) test) factor))
      (@eq_trans _ _ _ _
        (@eq_ap (Hom C B0 D1) (Hom C T D1)
          (λ h : τ (Hom C B0 D1), @comp_fapp0 C T B0 D1 h (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@comp_fapp0 C T A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1) test) factor))
          _ _ (@computational_chain_pair_map_lower_path C S A0 B0 D0 A1 B1 D1 p0 p1 F))
        (@eq_trans _ _ _ _
          (@eq_sym _ _ _ (@comp_assoc C T B0 B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@comp_fapp0 C T A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1) test) factor)))
          (@eq_trans _ _ _ _
            (@eq_ap (Hom C T B1) (Hom C T D1)
              (λ h : τ (Hom C T B1), @comp_fapp0 C T B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) h)
              _ _ (@hom_postcomp_factor_path C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@comp_fapp0 C T A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1) test) factor))
            (@eq_trans _ _ _ _
              (@comp_assoc C T A1 B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) (@computational_chain_pair_dnext C S A1 B1 D1 p1) test)
              (@preadditive_precompose_zero_path C S T A1 D1
                (@comp_fapp0 C A1 B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) (@computational_chain_pair_dnext C S A1 B1 D1 p1)) test
                (@computational_chain_pair_path C S A1 B1 D1 p1)))))));

// Retain the factor arrow and the derived cycle equation in the existing fibre.
symbol chain_pair_map_factor_cycle_cone
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  (lower_monic : τ (@IsMonic C D0 D1 (@computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 F)))
  (T : τ (Obj C))
  (test : τ (Hom C T A1))
  (factor : τ (@HomPostcompFactor C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@comp_fapp0 C T A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1) test)))
  : τ (@WeakKernelAnnihilator C S B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0) T)
≔ @Struct_sigma (Hom C T B0)
    (λ h : τ (Hom C T B0), @= (Hom C T D0)
      (@comp_fapp0 C T B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0) h)
      (@preadditive_hom_zero C S T D0))
    (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@comp_fapp0 C T A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1) test) factor)
    (@chain_pair_map_factor_cycle_zero_path C S A0 B0 D0 A1 B1 D1 p0 p1 F lower_monic T test factor);

// Select the lift through the original, explicitly supplied whole kernel.
symbol chain_pair_map_factor_cycle_lift
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  (lower_monic : τ (@IsMonic C D0 D1 (@computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 F)))
  (T : τ (Obj C))
  (test : τ (Hom C T A1))
  (factor : τ (@HomPostcompFactor C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@comp_fapp0 C T A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1) test)))
  (K : τ (@ComputationalKernel C S B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0)))
  : τ (Hom C T (@computational_kernel_object C S B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0) K))
≔ @computational_kernel_lift C S B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0) K T (@chain_pair_map_factor_cycle_cone C S A0 B0 D0 A1 B1 D1 p0 p1 F lower_monic T test factor);

// Its reconstruction uses the original kernel embedding and factor arrow.
symbol chain_pair_map_factor_cycle_lift_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  (lower_monic : τ (@IsMonic C D0 D1 (@computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 F)))
  (T : τ (Obj C))
  (test : τ (Hom C T A1))
  (factor : τ (@HomPostcompFactor C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@comp_fapp0 C T A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1) test)))
  (K : τ (@ComputationalKernel C S B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0)))
  : τ (@= (Hom C T B0)
      (@comp_fapp0 C T (@computational_kernel_object C S B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0) K) B0 (@computational_kernel_morphism C S B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0) K) (@chain_pair_map_factor_cycle_lift C S A0 B0 D0 A1 B1 D1 p0 p1 F lower_monic T test factor K))
      (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@comp_fapp0 C T A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1) test) factor))
≔ @computational_kernel_lift_path C S B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0) K T (@chain_pair_map_factor_cycle_cone C S A0 B0 D0 A1 B1 D1 p0 p1 F lower_monic T test factor);
