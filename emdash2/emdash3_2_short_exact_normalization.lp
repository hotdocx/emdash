/* Normalize using the existing whole image kernel and selected comparison isomorphisms. */

require open emdash.emdash3_2_short_exact_normalization_projections;
require open emdash.emdash3_2_short_exact_normalization_isos;
require open emdash.emdash3_2_monic_selected_row_comparison;

symbol short_exact_normalization_source_factor
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  : τ (@ShortExactNormalizationSourceComparison C P t Ab A B D pair
    (@selected_short_exact_row C P t (@computational_abelian_preabelian C P t Ab) A B
    (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair)))
≔ @monic_selected_row_comparison C P t (@computational_abelian_preabelian C P t Ab) A B
  (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair)
    (@computational_abelian_mono_lifts C P t Ab)
    (@computational_short_exact_monic C P t
      (@computational_abelian_preabelian C P t Ab) A B D pair short);

symbol short_exact_normalization_target_factor
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  : τ (@ShortExactNormalizationTargetComparison C P t Ab A B D pair
    (@selected_short_exact_row C P t (@computational_abelian_preabelian C P t Ab) A B
    (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair)))
≔ @Struct_sigma (@IsoEvidence C (@computational_cokernel_object C (@additive_preadditive C P t
  (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B
  (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
  (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair))) D)
    (λ e : τ (@IsoEvidence C (@computational_cokernel_object C (@additive_preadditive C P t
      (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B
      (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t
      (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
      (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
      (@additive_preadditive C P t (@preabelian_additive C P t
      (@computational_abelian_preabelian C P t Ab))) A B D pair))) D), @= (Hom C B D)
      (@comp_fapp0 C _ _ _ (@iso_evidence_to C (@computational_cokernel_object C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
        (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair))) D e)
        (@computational_chain_pair_d C (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) (@computational_kernel_object C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) B (@computational_cokernel_object C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
        (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair)))
        (@computational_cokernel_morphism C (@additive_preadditive C P t
        (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B
        (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
        (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair))) (@computational_image C P t
        (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair))) B
        (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
        (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair)))
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
        (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) B (@computational_cokernel_object C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
        (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair)))
        (@computational_cokernel_morphism C (@additive_preadditive C P t
        (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B
        (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
        (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair))) (@computational_image C P t
        (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair))) B
        (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
        (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair)))
        (@selected_short_exact_row C P t (@computational_abelian_preabelian C P t Ab) A B
        (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair)))))
      (@computational_chain_pair_d C (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair))
    (@short_exact_normalization_target_iso C P t Ab A B D pair short)
    (@short_exact_cokernel_comparison_path C P t Ab A B D pair);

symbol short_exact_normalization
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  : τ (@ShortExactNormalization C P t Ab A B D pair)
≔ @short_exact_normalization_intro C P t Ab A B D pair
    (@selected_short_exact_row C P t (@computational_abelian_preabelian C P t Ab) A B
      (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t
      (@computational_abelian_preabelian C P t Ab))) A B D pair))
    (@short_exact_normalization_source_factor C P t Ab A B D pair short)
    (@short_exact_normalization_target_factor C P t Ab A B D pair short);
