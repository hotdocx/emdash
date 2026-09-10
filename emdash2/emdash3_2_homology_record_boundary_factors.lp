/* A cycle factor of an incoming boundary is killed by the retained quotient. */
require open emdash.emdash3_2_computational_homology;
require open emdash.emdash3_2_hom_factor_composition;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

symbol homology_record_boundary_multiple
  [C : Cat] [S : τ (@PreadditiveCategory C)] [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D))
  (H : τ (@HomologyRecord C S A B D pair))
  (T : τ (Obj C)) (v : τ (Hom C T A))
  : τ (@HomPostcompFactor C (@homology_record_cycle_object C S A B D pair H) B T (@homology_record_cycle_embedding C S A B D pair H)
    (@comp_fapp0 C T A B (@computational_chain_pair_dnext C S A B D pair) v))
≔ @hom_postcomp_factor_paste C T A A A (@homology_record_cycle_object C S A B D pair H) B v (@id C A)
  (@homology_record_cycle_embedding C S A B D pair H) (@id C A) (@computational_chain_pair_dnext C S A B D pair)
    (@hom_postcomp_factor_intro C A A T (@id C A) v v (@eq_refl (Hom C T A) v))
    (@homology_record_boundary_factor C S A B D pair H);

symbol homology_record_boundary_factor_path
  [C : Cat] [S : τ (@PreadditiveCategory C)] [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D))
  (H : τ (@HomologyRecord C S A B D pair))
  (T : τ (Obj C)) (v : τ (Hom C T A))
  (F : τ (@HomPostcompFactor C (@homology_record_cycle_object C S A B D pair H) B T (@homology_record_cycle_embedding C S A B D pair
    H) (@comp_fapp0 C T A B (@computational_chain_pair_dnext C S A B D pair) v)))
  : τ (@= (Hom C T (@homology_record_cycle_object C S A B D pair H)) (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C
    S A B D pair H) B T (@homology_record_cycle_embedding C S A B D pair H) (@comp_fapp0 C T A B (@computational_chain_pair_dnext C
    S A B D pair) v) F) (@comp_fapp0 C T A (@homology_record_cycle_object C S A B D pair H) (@homology_record_boundary C S A B D
    pair H) v))
≔ (@computational_kernel_morphism_is_monic C S B D (@computational_chain_pair_d C S A B D pair) (@homology_record_cycles C S A B D
  pair H)) T
    (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A B D pair H) B T (@homology_record_cycle_embedding C S A B D
      pair H) (@comp_fapp0 C T A B (@computational_chain_pair_dnext C S A B D pair) v) F) (@comp_fapp0 C T A
      (@homology_record_cycle_object C S A B D pair H) (@homology_record_boundary C S A B D pair H) v)
    (@eq_trans _ _ _ _
      (@hom_postcomp_factor_path C (@homology_record_cycle_object C S A B D pair H) B T (@homology_record_cycle_embedding C S A B D
        pair H) (@comp_fapp0 C T A B (@computational_chain_pair_dnext C S A B D pair) v) F)
      (@eq_sym _ _ _ (@hom_postcomp_factor_path C (@homology_record_cycle_object C S A B D pair H) B T
        (@homology_record_cycle_embedding C S A B D pair H) (@comp_fapp0 C T A B (@computational_chain_pair_dnext C S A B D pair) v)
        (@homology_record_boundary_multiple C S A B D pair H T v))));

symbol homology_record_boundary_factor_zero
  [C : Cat] [S : τ (@PreadditiveCategory C)] [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D))
  (H : τ (@HomologyRecord C S A B D pair))
  (T : τ (Obj C)) (v : τ (Hom C T A))
  (F : τ (@HomPostcompFactor C (@homology_record_cycle_object C S A B D pair H) B T (@homology_record_cycle_embedding C S A B D pair
    H) (@comp_fapp0 C T A B (@computational_chain_pair_dnext C S A B D pair) v)))
  : τ (@= (Hom C T (@homology_record_object C S A B D pair H)) (@comp_fapp0 C T (@homology_record_cycle_object C S A B D pair H)
    (@homology_record_object C S A B D pair H) (@homology_record_projection C S A B D pair H) (@hom_postcomp_factor_arrow C
    (@homology_record_cycle_object C S A B D pair H) B T (@homology_record_cycle_embedding C S A B D pair H) (@comp_fapp0 C T A B
    (@computational_chain_pair_dnext C S A B D pair) v) F))
    (@preadditive_hom_zero C S T (@homology_record_object C S A B D pair H)))
≔ @eq_trans _ _ _ _
    (@eq_ap (Hom C T (@homology_record_cycle_object C S A B D pair H)) (Hom C T (@homology_record_object C S A B D pair H))
      (λ h : τ (Hom C T (@homology_record_cycle_object C S A B D pair H)), @comp_fapp0 C T (@homology_record_cycle_object C S A B D
        pair H) (@homology_record_object C S A B D pair H) (@homology_record_projection C S A B D pair H) h) _ _
      (@homology_record_boundary_factor_path C S A B D pair H T v F))
    (@eq_trans _ _ _ _
      (@comp_assoc C T A (@homology_record_cycle_object C S A B D pair H) (@homology_record_object C S A B D pair H)
        (@homology_record_projection C S A B D pair H) (@homology_record_boundary C S A B D pair H) v)
      (@preadditive_precompose_zero_path C S T A (@homology_record_object C S A B D pair H)
        (@comp_fapp0 C A (@homology_record_cycle_object C S A B D pair H) (@homology_record_object C S A B D pair H)
          (@homology_record_projection C S A B D pair H) (@homology_record_boundary C S A B D pair H)) v
        (@homology_record_projection_path C S A B D pair H)));
