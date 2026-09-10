/*
  Lift a middle cycle through an existing chain-map factor.
  The retained source kernel supplies the lift, and actual cycle/quotient
  reconstruction factors identify its image. No alternative H-map is chosen.
*/
require open emdash.emdash3_2_chain_pair_cycle_factors;
require open emdash.emdash3_2_homology_record_cancellation;
require open emdash.emdash3_2_hom_factor_composition;

symbol homology_record_cycle_lift_factor [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (H0 : τ (@HomologyRecord C S A0 B0 D0 p0))
  (H1 : τ (@HomologyRecord C S A1 B1 D1 p1))
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  (lower_monic : τ (@IsMonic C D0 D1 (@computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 m)))
  (T : τ (Obj C)) (w : τ (Hom C T (@homology_record_cycle_object C S A1 B1 D1 p1 H1)))
  (factor : τ (@HomPostcompFactor C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m)
    (@comp_fapp0 C T (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)
      w)))
  : τ (@HomPostcompFactor C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 T (@homology_record_cycle_embedding C S A0 B0 D0
    p0 H0) (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@comp_fapp0 C
    T (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) w) factor))
≔ is_contr_center (@computational_kernel_factor_contr C S B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0)
    (@homology_record_cycles C S A0 B0 D0 p0 H0) T (@chain_pair_map_cycle_factor_cone C S A0 B0 D0 A1 B1 D1 p0 p1 m lower_monic T
      (@computational_kernel_monic_cone C S B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) (@homology_record_cycles C S A1 B1
      D1 p1 H1) T w) factor));

symbol homology_record_cycle_lift_image_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (H0 : τ (@HomologyRecord C S A0 B0 D0 p0))
  (H1 : τ (@HomologyRecord C S A1 B1 D1 p1))
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  (lower_monic : τ (@IsMonic C D0 D1 (@computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 m)))
  (T : τ (Obj C)) (w : τ (Hom C T (@homology_record_cycle_object C S A1 B1 D1 p1 H1)))
  (factor : τ (@HomPostcompFactor C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m)
    (@comp_fapp0 C T (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)
      w))) (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A0
      B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0
      p0 H0) B0 B1 (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@homology_record_cycle_embedding C S A0 B0
      D0 p0 H0))))
  : τ (@= (Hom C T (@homology_record_cycle_object C S A1 B1 D1 p1 H1)) (@comp_fapp0 C T (@homology_record_cycle_object C S A0 B0 D0
    p0 H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A1 B1
    D1 p1 H1) B1 (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)
    (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 B1 (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1
    D1 p0 p1 m) (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)) cf) (@hom_postcomp_factor_arrow C
    (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 T (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)
    (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@comp_fapp0 C T
    (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) w) factor)
    (@homology_record_cycle_lift_factor C S A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 m lower_monic T w factor))) w)
≔ (@homology_record_cycle_monic C S A1 B1 D1 p1 H1) T
    (@comp_fapp0 C T (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1)
      (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A0 B0
      D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0
      H0) B0 B1 (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@homology_record_cycle_embedding C S A0 B0 D0
      p0 H0)) cf) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 T
      (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0) (@hom_postcomp_factor_arrow C B0 B1 T
      (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@comp_fapp0 C T (@homology_record_cycle_object C S A1 B1
      D1 p1 H1) B1 (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) w) factor) (@homology_record_cycle_lift_factor C S A0 B0 D0
      A1 B1 D1 p0 p1 H0 H1 m lower_monic T w factor))) w
    (@eq_trans _ _ _ _
      (@hom_postcomp_factor_path C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 T (@homology_record_cycle_embedding C S A1
        B1 D1 p1 H1) (@comp_fapp0 C T B0 B1 (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m)
        (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@comp_fapp0 C T
        (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) w) factor))
        (@hom_postcomp_factor_paste C T T (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 (@homology_record_cycle_object C S
          A1 B1 D1 p1 H1) B1
          (@id C T) (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)
            (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@comp_fapp0
            C T (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) w)
            factor) (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@homology_record_cycle_lift_factor C S A0
            B0 D0 A1 B1 D1 p0 p1 H0 H1 m lower_monic T w factor) cf))
      (@hom_postcomp_factor_path C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m)
        (@comp_fapp0 C T (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)
          w) factor));

symbol homology_record_cycle_lift_homology_factor [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (H0 : τ (@HomologyRecord C S A0 B0 D0 p0))
  (H1 : τ (@HomologyRecord C S A1 B1 D1 p1))
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  (lower_monic : τ (@IsMonic C D0 D1 (@computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 m)))
  (T : τ (Obj C)) (w : τ (Hom C T (@homology_record_cycle_object C S A1 B1 D1 p1 H1)))
  (factor : τ (@HomPostcompFactor C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m)
    (@comp_fapp0 C T (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)
      w)))
  (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A0 B0 D0 p0
    H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0
    B1 (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0))))
    (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A0 B0 D0 p0 H0)
    (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection C S A0 B0 D0 p0 H0) (@comp_fapp0 C
    (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@homology_record_object C
    S A1 B1 D1 p1 H1) (@homology_record_projection C S A1 B1 D1 p1 H1) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object
    C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)
    (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 B1 (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1
    D1 p0 p1 m) (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)) cf))))
  : τ (@HomPostcompFactor C (@homology_record_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A1 B1 D1 p1 H1) T
    (@hom_precomp_factor_arrow C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A0 B0 D0 p0 H0)
    (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection C S A0 B0 D0 p0 H0) (@comp_fapp0 C
    (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@homology_record_object C
    S A1 B1 D1 p1 H1) (@homology_record_projection C S A1 B1 D1 p1 H1) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object
    C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)
    (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 B1 (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1
    D1 p0 p1 m) (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)) cf)) hf)
      (@comp_fapp0 C T (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@homology_record_object C S A1 B1 D1 p1 H1)
        (@homology_record_projection C S A1 B1 D1 p1 H1) w))
≔ @hom_postcomp_factor_intro C (@homology_record_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A1 B1 D1 p1 H1) T
  (@hom_precomp_factor_arrow C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A0 B0 D0 p0 H0)
  (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection C S A0 B0 D0 p0 H0) (@comp_fapp0 C
  (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@homology_record_object C S
  A1 B1 D1 p1 H1) (@homology_record_projection C S A1 B1 D1 p1 H1) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S
  A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)
  (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 B1 (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1
  D1 p0 p1 m) (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)) cf)) hf)
    (@comp_fapp0 C T (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@homology_record_object C S A1 B1 D1 p1 H1)
      (@homology_record_projection C S A1 B1 D1 p1 H1) w) (@comp_fapp0 C T (@homology_record_cycle_object C S A0 B0 D0 p0 H0)
      (@homology_record_object C S A0 B0 D0 p0 H0) (@homology_record_projection C S A0 B0 D0 p0 H0) (@hom_postcomp_factor_arrow C
      (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 T (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)
      (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@comp_fapp0 C T
      (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) w) factor)
      (@homology_record_cycle_lift_factor C S A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 m lower_monic T w factor)))
    (@eq_trans _ _ _ _
      (@eq_sym _ _ _
        (@hom_factor_paste_path C T T (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A0 B0 D0 p0
          H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@homology_record_object C S A1 B1 D1 p1 H1)
          (@id C T) (@homology_record_projection C S A0 B0 D0 p0 H0) (@homology_record_projection C S A1 B1 D1 p1 H1)
            (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 T (@homology_record_cycle_embedding
            C S A0 B0 D0 p0 H0) (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0
            p1 m) (@comp_fapp0 C T (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_embedding C S A1 B1
            D1 p1 H1) w) factor) (@homology_record_cycle_lift_factor C S A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 m lower_monic T w factor))
            (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S
            A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) (@comp_fapp0 C (@homology_record_cycle_object C S
            A0 B0 D0 p0 H0) B0 B1 (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m)
            (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)) cf) (@comp_fapp0 C T (@homology_record_cycle_object C S A0 B0 D0
            p0 H0) (@homology_record_object C S A0 B0 D0 p0 H0) (@homology_record_projection C S A0 B0 D0 p0 H0)
            (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 T (@homology_record_cycle_embedding
            C S A0 B0 D0 p0 H0) (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0
            p1 m) (@comp_fapp0 C T (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_embedding C S A1 B1
            D1 p1 H1) w) factor) (@homology_record_cycle_lift_factor C S A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 m lower_monic T w factor)))
            (@hom_precomp_factor_arrow C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A0 B0 D0 p0
            H0) (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection C S A0 B0 D0 p0 H0) (@comp_fapp0 C
            (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1)
            (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection C S A1 B1 D1 p1 H1)
            (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S
            A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) (@comp_fapp0 C (@homology_record_cycle_object C S
            A0 B0 D0 p0 H0) B0 B1 (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m)
            (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)) cf)) hf)
          (@eq_refl (Hom C T (@homology_record_object C S A0 B0 D0 p0 H0)) (@comp_fapp0 C T (@homology_record_cycle_object C S A0 B0
            D0 p0 H0) (@homology_record_object C S A0 B0 D0 p0 H0) (@homology_record_projection C S A0 B0 D0 p0 H0)
            (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 T (@homology_record_cycle_embedding
            C S A0 B0 D0 p0 H0) (@hom_postcomp_factor_arrow C B0 B1 T (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0
            p1 m) (@comp_fapp0 C T (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_embedding C S A1 B1
            D1 p1 H1) w) factor) (@homology_record_cycle_lift_factor C S A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 m lower_monic T w factor))))
          (@eq_sym _ _ _ (@hom_precomp_factor_path C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_object C S
            A0 B0 D0 p0 H0) (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection C S A0 B0 D0 p0 H0)
            (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1)
            (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection C S A1 B1 D1 p1 H1)
            (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S
            A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) (@comp_fapp0 C (@homology_record_cycle_object C S
            A0 B0 D0 p0 H0) B0 B1 (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m)
            (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)) cf)) hf))))
      (@eq_ap (Hom C T (@homology_record_cycle_object C S A1 B1 D1 p1 H1)) (Hom C T (@homology_record_object C S A1 B1 D1 p1 H1))
        (λ v : τ (Hom C T (@homology_record_cycle_object C S A1 B1 D1 p1 H1)), @comp_fapp0 C T (@homology_record_cycle_object C S A1
          B1 D1 p1 H1) (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection C S A1 B1 D1 p1 H1) v) _ _
        (@homology_record_cycle_lift_image_path C S A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 m lower_monic T w factor cf)));
