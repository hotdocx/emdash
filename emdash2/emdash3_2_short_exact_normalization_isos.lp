/* Canonical isomorphisms at the common image/cokernel endpoints. */

require open emdash.emdash3_2_short_exact_normalization_foundation;

symbol short_exact_normalization_source_iso
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  : τ (@IsoEvidence C A (@computational_kernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) B
    (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair)))
    (@computational_cokernel_morphism C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair))) (@computational_image C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair))))
≔ @monic_image_iso C P t (@computational_abelian_preabelian C P t Ab) A B
  (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair)
    (@computational_abelian_mono_lifts C P t Ab)
    (@computational_short_exact_monic C P t
      (@computational_abelian_preabelian C P t Ab) A B D pair short);

symbol short_exact_normalization_target_iso
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  : τ (@IsoEvidence C (@computational_cokernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B
    (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair))) D)
≔ @short_exact_cokernel_comparison_iso C P t Ab A B D pair short;
