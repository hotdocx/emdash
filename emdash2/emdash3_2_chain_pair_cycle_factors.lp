/*
  A factor of any target cycle is a source cycle when the lower map is monic.
  This extends the incoming-boundary-only cycle-factor interface; the
  original chain-map components and target cycle witness remain the inputs.
*/
require open emdash.emdash3_2_chain_pair_maps;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

symbol chain_pair_map_cycle_factor_zero
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) (lower_monic : τ (@IsMonic C D0 D1
    (@computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 m)))
  (T : τ (Obj C)) (cycle : τ (@WeakKernelAnnihilator C S B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) T)) (factor : τ
    (@HomPostcompFactor C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m)
    (@weak_kernel_annihilator_arrow C S B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) T cycle)))
  : τ (@= (Hom C T D0) (@comp_fapp0 C T B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0) (@hom_postcomp_factor_arrow C B0 B1 T
    (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@weak_kernel_annihilator_arrow C S B1 D1
    (@computational_chain_pair_d C S A1 B1 D1 p1) T cycle) factor))
      (@preadditive_hom_zero C S T D0))
≔ @monic_postcomposition_zero_to_zero_path C S T D0 D1 (@computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 m)
  lower_monic
    (@comp_fapp0 C T B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0) (@hom_postcomp_factor_arrow C B0 B1 T
      (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@weak_kernel_annihilator_arrow C S B1 D1
      (@computational_chain_pair_d C S A1 B1 D1 p1) T cycle) factor))
    (@eq_trans _ _ _ _
      (@comp_assoc C T B0 D0 D1 (@computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@computational_chain_pair_d C S
        A0 B0 D0 p0) (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m)
        (@weak_kernel_annihilator_arrow C S B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) T cycle) factor))
      (@eq_trans _ _ _ _
        (@eq_ap (Hom C B0 D1) (Hom C T D1)
          (λ h : τ (Hom C B0 D1), @comp_fapp0 C T B0 D1 h (@hom_postcomp_factor_arrow C B0 B1 T
            (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@weak_kernel_annihilator_arrow C S B1 D1
            (@computational_chain_pair_d C S A1 B1 D1 p1) T cycle) factor)) _ _
          (@computational_chain_pair_map_lower_path C S A0 B0 D0 A1 B1 D1 p0 p1 m))
        (@eq_trans _ _ _ _
          (@eq_sym _ _ _ (@comp_assoc C T B0 B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1)
            (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@hom_postcomp_factor_arrow C B0 B1 T
            (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@weak_kernel_annihilator_arrow C S B1 D1
            (@computational_chain_pair_d C S A1 B1 D1 p1) T cycle) factor)))
          (@eq_trans _ _ _ _
            (@eq_ap (Hom C T B1) (Hom C T D1)
              (λ h : τ (Hom C T B1), @comp_fapp0 C T B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) h) _ _
              (@hom_postcomp_factor_path C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m)
                (@weak_kernel_annihilator_arrow C S B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) T cycle) factor))
            (@weak_kernel_annihilator_path C S B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) T cycle)))));

symbol chain_pair_map_cycle_factor_cone
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) (lower_monic : τ (@IsMonic C D0 D1
    (@computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 m)))
  (T : τ (Obj C)) (cycle : τ (@WeakKernelAnnihilator C S B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) T)) (factor : τ
    (@HomPostcompFactor C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m)
    (@weak_kernel_annihilator_arrow C S B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) T cycle)))
  : τ (@WeakKernelAnnihilator C S B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0) T)
≔ @Struct_sigma (Hom C T B0)
    (λ h : τ (Hom C T B0), @= (Hom C T D0)
      (@comp_fapp0 C T B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0) h) (@preadditive_hom_zero C S T D0))
    (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m)
      (@weak_kernel_annihilator_arrow C S B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) T cycle) factor)
      (@chain_pair_map_cycle_factor_zero C S A0 B0 D0 A1 B1 D1 p0 p1 m lower_monic T cycle factor);
