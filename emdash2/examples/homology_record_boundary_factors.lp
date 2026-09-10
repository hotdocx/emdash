/* Boundary-factor operations retain the supplied homology and actual beta. */
require open emdash.emdash3_2_homology_record_boundary_factors;

assert [C : Cat] [S : τ (@PreadditiveCategory C)] [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D))
  (H : τ (@HomologyRecord C S A B D pair)) ⊢
  @hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A B D pair H) B A (@homology_record_cycle_embedding C S A B D pair H) (@computational_chain_pair_dnext C S A B D pair)
    (@homology_record_boundary_multiple C S A B D pair H A (@id C A))
  ≡ (@homology_record_boundary C S A B D pair H);

assert [C : Cat] [S : τ (@PreadditiveCategory C)] [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D))
  (H : τ (@HomologyRecord C S A B D pair)) [T : τ (Obj C)] (v : τ (Hom C T A))
  (F : τ (@HomPostcompFactor C (@homology_record_cycle_object C S A B D pair H) B T (@homology_record_cycle_embedding C S A B D pair H)
    (@comp_fapp0 C T A B (@computational_chain_pair_dnext C S A B D pair) v))) ⊢
  @homology_record_boundary_factor_zero C S A B D pair H T v F
  : τ (@= (Hom C T (@homology_record_object C S A B D pair H))
      (@comp_fapp0 C T (@homology_record_cycle_object C S A B D pair H) (@homology_record_object C S A B D pair H)
        (@homology_record_projection C S A B D pair H)
        (@hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A B D pair H) B T (@homology_record_cycle_embedding C S A B D pair H)
          (@comp_fapp0 C T A B (@computational_chain_pair_dnext C S A B D pair) v) F))
      (@preadditive_hom_zero C S T (@homology_record_object C S A B D pair H)));
