/*
  Cancellation and zero composites at retained homology records.
  The factors consumed here can be supplied by whole H naturality. No map
  or homology is reselected, and no independent map algorithm is introduced.
*/
require open emdash.emdash3_2_homology_record_boundary_factors;

symbol homology_record_cycle_monic [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  (H : τ (@HomologyRecord C S A B D pair))
  : τ (@IsMonic C (@homology_record_cycle_object C S A B D pair H) B (@homology_record_cycle_embedding C S A B D pair H))
≔ @computational_kernel_morphism_is_monic C S B D (@computational_chain_pair_d C S A B D pair) (@homology_record_cycles C S A B D
  pair H);

symbol homology_record_projection_epic [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  (H : τ (@HomologyRecord C S A B D pair))
  : τ (@IsEpic C (@homology_record_cycle_object C S A B D pair H) (@homology_record_object C S A B D pair H)
    (@homology_record_projection C S A B D pair H))
≔ @computational_cokernel_morphism_is_epic C S A (@homology_record_cycle_object C S A B D pair H) (@homology_record_boundary C S A B
  D pair H) (@homology_record_cokernel C S A B D pair H);

symbol homology_record_cycle_factor_zero
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (H0 : τ (@HomologyRecord C S A0 B0 D0 p0))
  (H1 : τ (@HomologyRecord C S A1 B1 D1 p1))
  (f : τ (Hom C B0 B1)) (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1
    (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) (@comp_fapp0 C
    (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 B1 f (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0))))
  (zero : τ (@= (Hom C B0 B1) f (@preadditive_hom_zero C S B0 B1)))
  : τ (@= (Hom C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1))
    (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A0 B0 D0
    p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0 H0)
    B0 B1 f (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)) cf) (@preadditive_hom_zero C S (@homology_record_cycle_object C S
    A0 B0 D0 p0 H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1)))
≔ @monic_postcomposition_zero_to_zero_path C S (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_object C S
  A1 B1 D1 p1 H1) B1 (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)
    (@homology_record_cycle_monic C S A1 B1 D1 p1 H1) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A1 B1 D1 p1
      H1) B1 (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) (@comp_fapp0 C
      (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 B1 f (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)) cf)
    (@eq_trans _ _ _ _
      (@hom_postcomp_factor_path C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A0 B0 D0
        p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0
        H0) B0 B1 f (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)) cf)
      (@preadditive_precompose_zero_path C S (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 B1 f
        (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0) zero));

symbol homology_record_map_factor_cycle_zero
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (H0 : τ (@HomologyRecord C S A0 B0 D0 p0))
  (H1 : τ (@HomologyRecord C S A1 B1 D1 p1))
  (f : τ (Hom C B0 B1)) (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1
    (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) (@comp_fapp0 C
    (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 B1 f (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)))) (hf : τ
    (@HomPrecompFactor C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A0 B0 D0 p0 H0)
    (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection C S A0 B0 D0 p0 H0) (@comp_fapp0 C
    (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@homology_record_object C
    S A1 B1 D1 p1 H1) (@homology_record_projection C S A1 B1 D1 p1 H1) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object
    C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)
    (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 B1 f (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0))
    cf))))
  (zero : τ (@= (Hom C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1))
    (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A0 B0 D0
    p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0 H0)
    B0 B1 f (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)) cf) (@preadditive_hom_zero C S (@homology_record_cycle_object C S
    A0 B0 D0 p0 H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1))))
  : τ (@= (Hom C (@homology_record_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A1 B1 D1 p1 H1))
    (@hom_precomp_factor_arrow C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A0 B0 D0 p0 H0)
    (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection C S A0 B0 D0 p0 H0) (@comp_fapp0 C
    (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@homology_record_object C
    S A1 B1 D1 p1 H1) (@homology_record_projection C S A1 B1 D1 p1 H1) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object
    C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)
    (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 B1 f (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0))
    cf)) hf) (@preadditive_hom_zero C S (@homology_record_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A1 B1 D1 p1 H1)))
≔ @epic_precomposition_zero_to_zero_path C S (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A0 B0
  D0 p0 H0) (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection C S A0 B0 D0 p0 H0)
    (@homology_record_projection_epic C S A0 B0 D0 p0 H0) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C S A0 B0 D0
      p0 H0) (@homology_record_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection
      C S A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_object C S A1 B1
      D1 p1 H1) (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection C S A1 B1 D1 p1 H1)
      (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A0 B0
      D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0
      H0) B0 B1 f (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)) cf)) hf)
    (@eq_trans _ _ _ _
      (@hom_precomp_factor_path C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A0 B0 D0 p0 H0)
        (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection C S A0 B0 D0 p0 H0) (@comp_fapp0 C
        (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1)
        (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection C S A1 B1 D1 p1 H1) (@hom_postcomp_factor_arrow C
        (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A0 B0 D0 p0 H0)
        (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0
        B1 f (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)) cf)) hf)
      (@preadditive_postcompose_zero_path C S (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_object C S
        A1 B1 D1 p1 H1) (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection C S A1 B1 D1 p1 H1)
        (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A0 B0
        D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0
        p0 H0) B0 B1 f (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)) cf) zero));

symbol homology_record_map_factor_middle_zero
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (H0 : τ (@HomologyRecord C S A0 B0 D0 p0))
  (H1 : τ (@HomologyRecord C S A1 B1 D1 p1))
  (f : τ (Hom C B0 B1)) (cf : τ (@HomPostcompFactor C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1
    (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) (@comp_fapp0 C
    (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 B1 f (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)))) (hf : τ
    (@HomPrecompFactor C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A0 B0 D0 p0 H0)
    (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection C S A0 B0 D0 p0 H0) (@comp_fapp0 C
    (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@homology_record_object C
    S A1 B1 D1 p1 H1) (@homology_record_projection C S A1 B1 D1 p1 H1) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object
    C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)
    (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 B1 f (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0))
    cf))))
  (zero : τ (@= (Hom C B0 B1) f (@preadditive_hom_zero C S B0 B1)))
  : τ (@= (Hom C (@homology_record_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A1 B1 D1 p1 H1))
    (@hom_precomp_factor_arrow C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A0 B0 D0 p0 H0)
    (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection C S A0 B0 D0 p0 H0) (@comp_fapp0 C
    (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@homology_record_object C
    S A1 B1 D1 p1 H1) (@homology_record_projection C S A1 B1 D1 p1 H1) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object
    C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)
    (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 B1 f (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0))
    cf)) hf) (@preadditive_hom_zero C S (@homology_record_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A1 B1 D1 p1 H1)))
≔ @homology_record_map_factor_cycle_zero C S A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 f cf hf
    (@homology_record_cycle_factor_zero C S A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 f cf zero);

symbol homology_record_map_factors_composite_zero
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (p2 : τ (@ComputationalChainPair C S A2 B2 D2))
  (H0 : τ (@HomologyRecord C S A0 B0 D0 p0))
  (H1 : τ (@HomologyRecord C S A1 B1 D1 p1))
  (H2 : τ (@HomologyRecord C S A2 B2 D2 p2))
  (f0 : τ (Hom C B0 B1)) (f1 : τ (Hom C B1 B2))
  (cf0 : τ (@HomPostcompFactor C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A0 B0 D0
    p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0 H0)
    B0 B1 f0 (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)))) (cf1 : τ (@HomPostcompFactor C (@homology_record_cycle_object
    C S A2 B2 D2 p2 H2) B2 (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@homology_record_cycle_embedding C S A2 B2 D2 p2 H2)
    (@comp_fapp0 C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 B2 f1 (@homology_record_cycle_embedding C S A1 B1 D1 p1
    H1))))
  (hf0 : τ (@HomPrecompFactor C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A0 B0 D0 p0 H0)
    (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_projection C S A0 B0 D0 p0 H0) (@comp_fapp0 C
    (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@homology_record_object C
    S A1 B1 D1 p1 H1) (@homology_record_projection C S A1 B1 D1 p1 H1) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object
    C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)
    (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 B1 f0 (@homology_record_cycle_embedding C S A0 B0 D0 p0
    H0)) cf0)))) (hf1 : τ (@HomPrecompFactor C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@homology_record_object C S A1 B1
    D1 p1 H1) (@homology_record_object C S A2 B2 D2 p2 H2) (@homology_record_projection C S A1 B1 D1 p1 H1) (@comp_fapp0 C
    (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@homology_record_cycle_object C S A2 B2 D2 p2 H2) (@homology_record_object C
    S A2 B2 D2 p2 H2) (@homology_record_projection C S A2 B2 D2 p2 H2) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object
    C S A2 B2 D2 p2 H2) B2 (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@homology_record_cycle_embedding C S A2 B2 D2 p2 H2)
    (@comp_fapp0 C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 B2 f1 (@homology_record_cycle_embedding C S A1 B1 D1 p1
    H1)) cf1))))
  (zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 f1 f0) (@preadditive_hom_zero C S B0 B2)))
  : τ (@= (Hom C (@homology_record_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A2 B2 D2 p2 H2))
      (@comp_fapp0 C (@homology_record_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A1 B1 D1 p1 H1)
        (@homology_record_object C S A2 B2 D2 p2 H2) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C S A1 B1 D1 p1 H1)
        (@homology_record_object C S A1 B1 D1 p1 H1) (@homology_record_object C S A2 B2 D2 p2 H2) (@homology_record_projection C S
        A1 B1 D1 p1 H1) (@comp_fapp0 C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@homology_record_cycle_object C S A2 B2
        D2 p2 H2) (@homology_record_object C S A2 B2 D2 p2 H2) (@homology_record_projection C S A2 B2 D2 p2 H2)
        (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A2 B2 D2 p2 H2) B2 (@homology_record_cycle_object C S A1 B1
        D1 p1 H1) (@homology_record_cycle_embedding C S A2 B2 D2 p2 H2) (@comp_fapp0 C (@homology_record_cycle_object C S A1 B1 D1
        p1 H1) B1 B2 f1 (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)) cf1)) hf1) (@hom_precomp_factor_arrow C
        (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A0 B0 D0 p0 H0) (@homology_record_object C S
        A1 B1 D1 p1 H1) (@homology_record_projection C S A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0
        p0 H0) (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@homology_record_object C S A1 B1 D1 p1 H1)
        (@homology_record_projection C S A1 B1 D1 p1 H1) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A1 B1 D1
        p1 H1) B1 (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)
        (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 B1 f0 (@homology_record_cycle_embedding C S A0 B0 D0 p0
        H0)) cf0)) hf0))
      (@preadditive_hom_zero C S (@homology_record_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A2 B2 D2 p2 H2)))
≔ @homology_record_map_factor_middle_zero C S A0 B0 D0 A2 B2 D2 p0 p2 H0 H2
    (@comp_fapp0 C B0 B1 B2 f1 f0) (@hom_postcomp_factor_paste C (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0
      (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1 (@homology_record_cycle_object C S A2 B2 D2 p2 H2) B2
      (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)
        (@homology_record_cycle_embedding C S A2 B2 D2 p2 H2) f0 f1 cf0 cf1) (@hom_precomp_factor_paste C
        (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_object C S A0 B0 D0 p0 H0)
        (@homology_record_cycle_object C S A1 B1 D1 p1 H1) (@homology_record_object C S A1 B1 D1 p1 H1)
        (@homology_record_cycle_object C S A2 B2 D2 p2 H2) (@homology_record_object C S A2 B2 D2 p2 H2)
      (@homology_record_projection C S A0 B0 D0 p0 H0) (@homology_record_projection C S A1 B1 D1 p1 H1) (@homology_record_projection
        C S A2 B2 D2 p2 H2) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A1 B1 D1 p1 H1) B1
        (@homology_record_cycle_object C S A0 B0 D0 p0 H0) (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1) (@comp_fapp0 C
        (@homology_record_cycle_object C S A0 B0 D0 p0 H0) B0 B1 f0 (@homology_record_cycle_embedding C S A0 B0 D0 p0 H0)) cf0)
        (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A2 B2 D2 p2 H2) B2 (@homology_record_cycle_object C S A1 B1
        D1 p1 H1) (@homology_record_cycle_embedding C S A2 B2 D2 p2 H2) (@comp_fapp0 C (@homology_record_cycle_object C S A1 B1 D1
        p1 H1) B1 B2 f1 (@homology_record_cycle_embedding C S A1 B1 D1 p1 H1)) cf1) hf0 hf1) zero;
